"""Numerical checks for the density-parameterized rank-two Schur model."""

from collections import defaultdict

import numpy as np


TOL = 1.0e-10


def density_parameters(p):
    """Return q, s, a, b, and delta for a central density p."""
    q = 1.0 - p
    s = np.sqrt(p * q)
    a = s / p
    b = s / q
    delta = b - a
    return q, s, a, b, delta


def central_endpoints():
    root5 = np.sqrt(5.0)
    return (5.0 - root5) / 10.0, (5.0 + root5) / 10.0


def alpha_c(epsilon, moment):
    """Pure coefficient and rank-one normal-form coefficients after all factors."""
    alpha = 1.0
    coeff = defaultdict(float)
    for n, scalar in enumerate(epsilon):
        next_coeff = defaultdict(float)
        for left in range(n + 1):
            value = alpha if left == n else 0.0
            for right in range(n + 1):
                value += coeff[(left, right)] * moment[right]
            if value:
                next_coeff[(left, 0)] += value
        for (left, right), value in coeff.items():
            next_coeff[(left, right + 1)] += scalar * value
        alpha = scalar * alpha
        coeff = next_coeff
    return alpha, coeff


def color_pattern(a, b, m):
    return [value for _ in range(m) for value in (a, -b)]


def cn(n, x, y):
    """The polynomial divided difference c_n(x,y)."""
    return sum((-1.0) ** r * x ** (2 * n - r) * y**r for r in range(2 * n + 1))


def density_beta(eigenvalues, coordinates, delta, n):
    """Weighted excursion coefficient from the spectral double sum."""
    weights = coordinates**2
    total = 0.0
    for i, x in enumerate(eigenvalues):
        for j, y in enumerate(eigenvalues):
            density_weight = 1.0 - delta * (x + y) / 2.0
            total += weights[i] * weights[j] * cn(n, x, y) * density_weight
    return float(total)


def random_model(dimension, p, seed):
    """A symmetric matrix, unit vector, and density parameters for algebraic checks."""
    rng = np.random.default_rng(seed)
    matrix = rng.normal(size=(dimension, dimension))
    matrix = (matrix + matrix.T) / 2.0
    matrix /= max(1.0, np.linalg.norm(matrix, ord="fro"))
    vector = rng.normal(size=dimension)
    vector /= np.linalg.norm(vector)
    q, s, a, b, delta = density_parameters(p)
    return matrix, vector, q, s, a, b, delta


def check_word(matrix, vector, a, b, m):
    """Compare the matrix word with its universal rank-one moment expression."""
    projection = np.outer(vector, vector)
    epsilon = color_pattern(a, b, m)
    length = 2 * m
    moment = [
        float(vector @ np.linalg.matrix_power(matrix, degree) @ vector)
        for degree in range(length + 1)
    ]
    word = np.eye(matrix.shape[0])
    for scalar in epsilon:
        word = word @ (projection + scalar * matrix)
    alpha, coeff = alpha_c(epsilon, moment)
    predicted = alpha * np.trace(np.linalg.matrix_power(matrix, length))
    predicted += sum(
        value * moment[left + right]
        for (left, right), value in coeff.items()
        if value != 0.0
    )
    expected_alpha = (-a * b) ** m
    return abs(np.trace(word) - predicted), abs(alpha - expected_alpha)


def check_schur(matrix, vector, a, b, delta, z):
    """Check the rank-two determinant factorization at a scalar z."""
    dimension = matrix.shape[0]
    identity = np.eye(dimension)
    projection = np.outer(vector, vector)
    product = (projection + a * matrix) @ (projection - b * matrix)
    resolvent = np.linalg.inv(identity + z * matrix @ matrix)
    h = vector @ resolvent @ vector
    k = vector @ matrix @ resolvent @ vector
    scalar_f = h**2 - delta * k + z * k**2
    lhs = np.linalg.det(identity - z * product)
    rhs = np.linalg.det(identity + z * matrix @ matrix) * (1.0 - z * scalar_f)
    return abs(lhs - rhs)


def check_beta_series(matrix, vector, delta, z, degree=12):
    """Compare F(z) with its truncated weighted-excursion expansion."""
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    coordinates = eigenvectors.T @ vector
    identity = np.eye(matrix.shape[0])
    resolvent = np.linalg.inv(identity + z * matrix @ matrix)
    h = vector @ resolvent @ vector
    k = vector @ matrix @ resolvent @ vector
    scalar_f = h**2 - delta * k + z * k**2
    truncated = sum(
        (-1.0) ** n * density_beta(eigenvalues, coordinates, delta, n) * z**n
        for n in range(degree + 1)
    )
    return abs(scalar_f - truncated)


def run_regressions():
    lower, upper = central_endpoints()
    densities = [lower, 0.35, 0.5, 0.65, upper]
    max_word_error = 0.0
    max_alpha_error = 0.0
    max_schur_error = 0.0
    max_series_error = 0.0
    max_parameter_error = 0.0

    for p in densities:
        q, s, a, b, delta = density_parameters(p)
        parameter_error = max(
            abs(a * b - 1.0),
            max(0.0, abs(delta) - 1.0),
            abs(s * s - p * q),
        )
        max_parameter_error = max(max_parameter_error, parameter_error)
        for dimension in (2, 4, 7, 10):
            for m in (3, 5, 7, 9):
                seed = 1000 * dimension + 10 * m + round(100 * p)
                matrix, vector, _, _, a, b, delta = random_model(dimension, p, seed)
                word_error, alpha_error = check_word(matrix, vector, a, b, m)
                max_word_error = max(max_word_error, word_error)
                max_alpha_error = max(max_alpha_error, alpha_error)
                max_schur_error = max(
                    max_schur_error,
                    check_schur(matrix, vector, a, b, delta, z=0.03125),
                )
                max_series_error = max(
                    max_series_error,
                    check_beta_series(matrix, vector, delta, z=0.01),
                )

    report = {
        "parameter_error": max_parameter_error,
        "word_error": max_word_error,
        "alpha_error": max_alpha_error,
        "schur_error": max_schur_error,
        "series_truncation_error": max_series_error,
    }
    assert report["parameter_error"] < TOL
    assert report["word_error"] < TOL
    assert report["alpha_error"] < TOL
    assert report["schur_error"] < TOL
    assert report["series_truncation_error"] < TOL
    return report


if __name__ == "__main__":
    print("Density-parameterized normal-form regressions")
    for name, error in run_regressions().items():
        print(f"  {name:26s} {error:.3e}")
