from fractions import Fraction


def target_fraction(numerator, denominator):
    if (type(numerator) is not int or type(denominator) is not int or
            numerator <= denominator or denominator <= 0):
        raise ValueError("target must be a rational number greater than one")
    return Fraction(numerator, denominator)


def vector_weight(vector, numerator, denominator):
    inverse = 1 / target_fraction(numerator, denominator)
    if (not isinstance(vector, list) or not vector or
            any(type(value) is not int for value in vector)):
        raise ValueError("branching vector must contain integers")
    return sum((inverse ** value for value in vector), Fraction(0, 1))


def check_vector(vector, numerator, denominator):
    if not vector or any(type(value) is not int or value <= 0 for value in vector):
        raise ValueError(f"all decreases must be positive integers: {vector}")
    total = vector_weight(vector, numerator, denominator)
    if total > 1:
        raise ValueError(f"branching vector {vector} violates the target")
