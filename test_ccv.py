import unittest
import random
import time
from credit_card_validator import credit_card_validator as ccv


class TestCCV(unittest.TestCase):
    def test1(self):
        """Test credit card validator using random testing.

        Generates random cards continuously until just before the 24 s
        limit, so the test count adapts to the machine it runs on.
        Distribution matches the original: 50/50 edge-case vs random
        length, 50/50 issuer prefix vs fully random digits.
        """
        time_limit = 24
        # Stop at 95% of the limit; the loop can overshoot by at most one
        # chunk (a few ms), leaving headroom for startup/teardown.
        deadline = time.perf_counter() + time_limit * 0.95

        # Edge cases
        length_edge_cases = [14, 15, 16, 17]

        # Generate prefix cases
        prefixes = ['4', '51', '52', '53', '54', '55', '34', '37']
        for i in range(2221, 2721):
            prefixes.append(str(i))

        # Hoist everything loop-invariant into locals: attribute lookups
        # are the main per-iteration overhead at this scale.
        choices = random.choices
        randrange = random.randrange
        perf_counter = time.perf_counter
        validator = ccv
        pow10 = [10 ** n for n in range(31)]
        all_lengths = range(1, 31)
        prefix_pairs = [(p, len(p)) for p in prefixes]
        # One draw from 4 equiprobable modes replaces the two separate
        # 50/50 coin flips: bit 0 = use edge-case length, bit 1 = prefix.
        modes4 = (0, 1, 2, 3)

        tests_generated = 0
        chunk = 8192
        while perf_counter() < deadline:
            # Pre-draw all randomness for the chunk in bulk; random.choices
            # is far cheaper per item than repeated randint/choice calls.
            modes = choices(modes4, k=chunk)
            edge_lens = choices(length_edge_cases, k=chunk)
            rand_lens = choices(all_lengths, k=chunk)
            pres = choices(prefix_pairs, k=chunk)
            for j in range(chunk):
                m = modes[j]
                length = edge_lens[j] if m & 1 else rand_lens[j]
                if m & 2:
                    card, plen = pres[j]
                    digits_left = length - plen
                    # One randrange + zfill builds the whole random tail,
                    # replacing the original per-digit randint loop.
                    if digits_left > 0:
                        card += str(randrange(pow10[digits_left])).zfill(
                            digits_left)
                else:
                    card = str(randrange(pow10[length])).zfill(length)
                validator(card)
            tests_generated += chunk

        print(f"\ntests generated: {tests_generated}")


if __name__ == "__main__":
    unittest.main()
