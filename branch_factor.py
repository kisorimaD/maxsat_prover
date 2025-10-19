import argparse

def branching_factor(vec, tol=1e-12):
    def f(x):
        return sum(x**(-a) for a in vec) - 1.0
    low = 1.0 + 1e-12
    high = 2.5
    for _ in range(60):
        if f(high) < 0:
            break
        high *= 1.5
    # binary search
    for _ in range(200):
        mid = (low + high) / 2.0
        if f(mid) > 0:
            low = mid
        else:
            high = mid
        if abs(high - low) < tol:
            break
    return (low + high) / 2.0



if __name__ == '__main__':
    parser = parser = argparse.ArgumentParser(
                        prog='Branching Factor Counter',
                        description='Computes branching factor of given branching vector',)

    parser.add_argument('vector', nargs='+')

    args = parser.parse_args()

    vec = args.vector

    print(f"{branching_factor(list(map(int, vec))):.5f}")