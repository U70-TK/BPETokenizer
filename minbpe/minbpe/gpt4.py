"""
Implements OpenAI-family pretrained tokenizers as a light wrapper around
RegexTokenizer. By default it loads `cl100k_base` from tiktoken, and it also
supports `o200k_base`.
"""

import json
from pathlib import Path

import tiktoken
from .regex import RegexTokenizer


def bpe(mergeable_ranks, token, max_rank):
    # helper function used in get_gpt4_merges() to reconstruct the merge forest
    parts = [bytes([b]) for b in token]
    while True:
        min_idx = None
        min_rank = None
        for i, pair in enumerate(zip(parts[:-1], parts[1:])):
            rank = mergeable_ranks.get(pair[0] + pair[1])
            if rank is not None and (min_rank is None or rank < min_rank):
                min_idx = i
                min_rank = rank
        if min_rank is None or (max_rank is not None and min_rank >= max_rank):
            break
        assert min_idx is not None
        parts = parts[:min_idx] + [parts[min_idx] + parts[min_idx + 1]] + parts[min_idx + 2:]
    return parts


def recover_merges(mergeable_ranks):
    # the `merges` are already the byte sequences in their merged state.
    # so we have to recover the original pairings. We can do this by doing
    # a small BPE training run on all the tokens, in their order.
    # also see https://github.com/openai/tiktoken/issues/60
    # also see https://github.com/karpathy/minbpe/issues/11#issuecomment-1950805306
    merges = {}
    for token, rank in mergeable_ranks.items():
        if len(token) == 1:
            continue # skip raw bytes
        pair = tuple(bpe(mergeable_ranks, token, max_rank=rank))
        assert len(pair) == 2
        # recover the integer ranks of the pair
        ix0 = mergeable_ranks[pair[0]]
        ix1 = mergeable_ranks[pair[1]]
        merges[(ix0, ix1)] = rank

    return merges

ENCODING_ALIASES = {
    "cl100k": "cl100k_base",
    "cl100k_base": "cl100k_base",
    "o200k": "o200k_base",
    "o200k_base": "o200k_base",
}


def byte_to_unicode():
    bs = list(range(ord("!"), ord("~") + 1))
    bs += list(range(ord("¡"), ord("¬") + 1))
    bs += list(range(ord("®"), ord("ÿ") + 1))
    cs = bs[:]
    n = 0
    for b in range(256):
        if b not in bs:
            bs.append(b)
            cs.append(256 + n)
            n += 1
    return dict(zip(bs, map(chr, cs)))


BYTE_TO_UNICODE = byte_to_unicode()
UNICODE_TO_BYTE = {v: k for k, v in BYTE_TO_UNICODE.items()}


def decode_token(token: str) -> bytes:
    return bytes(UNICODE_TO_BYTE[c] for c in token)


def load_encoding_from_tokenizer_json(tokenizer_path: str | Path):
    with open(tokenizer_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    pat_str = data["pre_tokenizer"]["pretokenizers"][0]["pattern"]["Regex"]
    mergeable_ranks = {
        decode_token(token): token_id for token, token_id in data["model"]["vocab"].items()
    }
    special_tokens = {
        entry["content"]: entry["id"]
        for entry in data.get("added_tokens", [])
        if entry.get("special")
    }
    merges = {}
    for raw in data["model"].get("merges", []):
        if isinstance(raw, str):
            parts = raw.split(" ")
            if len(parts) != 2:
                continue
            left_s, right_s = parts
        elif isinstance(raw, list) and len(raw) == 2:
            left_s, right_s = raw
        else:
            continue
        if not isinstance(left_s, str) or not isinstance(right_s, str):
            continue
        left_b = decode_token(left_s)
        right_b = decode_token(right_s)
        target_b = left_b + right_b
        left_id = mergeable_ranks.get(left_b)
        right_id = mergeable_ranks.get(right_b)
        target_id = mergeable_ranks.get(target_b)
        if left_id is None or right_id is None or target_id is None:
            continue
        merges[(left_id, right_id)] = target_id
    return pat_str, mergeable_ranks, special_tokens, merges

class GPT4Tokenizer(RegexTokenizer):
    """Lightweight wrapper on RegexTokenizer for cl100k/o200k tokenizers."""

    def __init__(self, encoding_name: str = "cl100k_base", tokenizer_path: str | None = None):
        merges_from_json = None
        if tokenizer_path is not None:
            pat_str, mergeable_ranks, special_tokens, merges_from_json = load_encoding_from_tokenizer_json(
                tokenizer_path
            )
            super().__init__(pattern=pat_str)
            self.encoding_name = f"json:{tokenizer_path}"
        else:
            resolved = ENCODING_ALIASES.get(encoding_name, encoding_name)
            if resolved not in ("cl100k_base", "o200k_base"):
                raise ValueError(
                    f"Unsupported encoding '{encoding_name}'. "
                    "Use one of: cl100k_base, cl100k, o200k_base, o200k."
                )
            # get the official tokenizer and its split pattern
            enc = tiktoken.get_encoding(resolved)
            super().__init__(pattern=enc._pat_str)
            self.encoding_name = resolved
            mergeable_ranks = enc._mergeable_ranks
            special_tokens = enc._special_tokens
        # Prefer explicit tokenizer.json merges if available; otherwise recover.
        if tokenizer_path is not None and merges_from_json:
            self.merges = merges_from_json
        else:
            self.merges = recover_merges(mergeable_ranks)
        # reconstruct the vocab from the merges
        def build_vocab(merges):
            vocab = {idx: bytes([idx]) for idx in range(256)}
            for (p0, p1), idx in sorted(merges.items(), key=lambda kv: kv[1]):
                vocab[idx] = vocab[p0] + vocab[p1]
            return vocab

        try:
            self.vocab = build_vocab(self.merges)
        except KeyError:
            # Some tokenizer.json merge lists are not dependency-ordered.
            # Fall back to merge recovery from mergeable ranks.
            self.merges = recover_merges(mergeable_ranks)
            self.vocab = build_vocab(self.merges)
        # now here is another tricky part.
        # for some reason, the tokens corresponding to individual bytes
        # are permuted in a different order. This is completely non-sensical
        # and probably historical, but therefore we have to deal with it here.
        self.byte_shuffle = {i: mergeable_ranks[bytes([i])] for i in range(256)}
        self.inverse_byte_shuffle = {v: k for k, v in self.byte_shuffle.items()}
        # finally register the special tokens of the selected encoding
        self.register_special_tokens(special_tokens)

    def _encode_chunk(self, text_bytes):
        # before we start processing bytes, we have to permute them
        text_bytes = bytes(self.byte_shuffle[b] for b in text_bytes)
        ids = super()._encode_chunk(text_bytes)
        return ids

    def decode(self, ids):
        # we have to un-permute the bytes before we decode
        text_bytes = b"".join(self.vocab[idx] for idx in ids)
        text_bytes = bytes(self.inverse_byte_shuffle[b] for b in text_bytes)
        text = text_bytes.decode("utf-8", errors="replace")
        return text

    # this is a pretrained tokenizer, it is not intended to be trained
    def train(self, text, vocab_size, verbose=False):
        raise NotImplementedError

    # save/load would require some thought.
    # we'd have to change save/load of base to add support for byte_shuffle...
    # alternatively, we could move byte_shuffle to base class, but that would
    # mean that we're making ugly our beautiful Tokenizer just to support
    # the GPT-4 tokenizer and its weird historical quirks around byte_shuffle.
    def save(self, file_prefix):
        raise NotImplementedError("GPT4Tokenizer cannot be saved.")

    def load(self, model_file):
        raise NotImplementedError("GPT4Tokenizer cannot be loaded.")

    def save_vocab(self, vocab_file):
        # just for visualization purposes let's output the GPT-4 tokens
        # in the exact same format as the base class would.
        # simple run as:
        # python -c "from minbpe import GPT4Tokenizer; GPT4Tokenizer().save_vocab('gpt4.vocab')"
        from .base import render_token
        # build vocab being mindful of the byte shuffle
        vocab = {idx: bytes([self.inverse_byte_shuffle[idx]]) for idx in range(256)}
        for (p0, p1), idx in self.merges.items():
            vocab[idx] = vocab[p0] + vocab[p1]
        # now merge the shuffled bytes and write to file
        inverted_merges = {idx: pair for pair, idx in self.merges.items()}
        with open(vocab_file, "w", encoding="utf-8") as f:
            for idx, token in vocab.items():
                s = render_token(token)
                if idx in inverted_merges:
                    idx0, idx1 = inverted_merges[idx]
                    s0 = render_token(vocab[idx0])
                    s1 = render_token(vocab[idx1])
                    f.write(f"[{s0}][{s1}] -> [{s}] {idx}\n")
                else:
                    f.write(f"[{s}] {idx}\n")
