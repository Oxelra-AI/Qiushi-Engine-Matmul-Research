import itertools
import unittest


def row_action(vector, matrix_rows):
    result = 0
    for i, row in enumerate(matrix_rows):
        if vector & (1 << i):
            result ^= row
    return result


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


class MatrixNormalizationTests(unittest.TestCase):
    def test_every_full_rank_lower_block_has_the_stated_coset_normal_form(self):
        gl3 = [rows for rows in itertools.product(range(1, 8), repeat=3)
               if binary_rank(rows) == 3]
        gl2 = [rows for rows in itertools.product(range(1, 4), repeat=2)
               if binary_rank(rows) == 2]
        blocks = [rows for rows in itertools.product(range(1, 8), repeat=2)
                  if binary_rank(rows) == 2]
        self.assertEqual((len(gl3), len(gl2), len(blocks)), (168, 6, 42))
        for block in blocks:
            with self.subTest(lower_block=block):
                witness = None
                for right in gl3:
                    transported = tuple(row_action(row, right) for row in block)
                    for lower_left in gl2:
                        normalized = tuple(row_action(row, transported)
                                           for row in lower_left)
                        if normalized == (2, 4):
                            witness = right, lower_left
                            break
                    if witness is not None:
                        break
                self.assertIsNotNone(witness)
                right, lower_left = witness
                # diag(1, lower_left) fixes e1; only the top row varies.
                images = set()
                for top in range(8):
                    transformed = tuple(row_action(row, right)
                                        for row in (top, *block))
                    images.add((transformed[0],
                                row_action(lower_left[0], transformed[1:]),
                                row_action(lower_left[1], transformed[1:])))
                self.assertEqual(images, {(top, 2, 4) for top in range(8)})


if __name__ == '__main__':
    unittest.main()
