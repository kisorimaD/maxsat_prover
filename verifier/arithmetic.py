from fractions import Fraction


def check_vector(vector, numerator, denominator):
    if not vector or any(type(value) is not int or value <= 0 for value in vector):
        raise ValueError(f"all decreases must be positive integers: {vector}")
    if numerator <= denominator or denominator <= 0:
        raise ValueError("target must be a rational number greater than one")
    inverse = Fraction(denominator, numerator)
    total = sum((inverse ** value for value in vector), Fraction(0, 1))
    if total > 1:
        raise ValueError(f"branching vector {vector} violates the target")

