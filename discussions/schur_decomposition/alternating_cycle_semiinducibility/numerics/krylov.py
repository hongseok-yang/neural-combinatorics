"""End-to-end numerical checks for fixed-density graphons and Krylov compression."""

import numpy as np

from normalform import alpha_c, central_endpoints, color_pattern, density_beta, density_parameters


TOL = 2.0e-9


def matrix_power_moments(matrix, vector, last_degree):
    return [
        float(vector @ np.linalg.matrix_power(matrix, degree) @ vector)
        for degree in range(last_degree + 1)
    ]


def fixed_density_graphon(p, size, seed):
    """Construct a symmetric [0,1]-valued matrix graphon with weighted mean p."""
    rng = np.random.default_rng(seed)
    raw = rng.normal(size=(size, size))
    raw = (raw + raw.T) / 2.0
    raw -= np.mean(raw)
    raw /= np.max(np.abs(raw))
    amplitude = 0.45 * min(p, 1.0 - p)
    graphon = p + amplitude * raw
    return graphon


def krylov_basis(matrix, vector, cutoff):
    vectors = np.stack(
        [np.linalg.matrix_power(matrix, degree) @ vector for degree in range(cutoff + 1)],
        axis=1,
    )
    left, singular_values, _ = np.linalg.svd(vectors, full_matrices=False)
    threshold = max(vectors.shape) * np.finfo(float).eps * singular_values[0]
    rank = int(np.count_nonzero(singular_values > threshold))
    return left[:, :rank]


def graphon_test(p, m, size=72, seed=0):
    """Check normalization, moment transport, monotonicity, and the main inequality."""
    graphon = fixed_density_graphon(p, size, seed)
    weights = np.full(size, 1.0 / size)
    sqrt_weight = np.diag(np.sqrt(weights))
    one = np.sqrt(weights)
    q, s, a, b, delta = density_parameters(p)

    centered = graphon - p
    normalized = centered / s
    red = sqrt_weight @ graphon @ sqrt_weight
    blue = sqrt_weight @ (1.0 - graphon) @ sqrt_weight
    centered_op = sqrt_weight @ centered @ sqrt_weight
    operator = sqrt_weight @ normalized @ sqrt_weight

    cutoff = 2 * m
    basis = krylov_basis(operator, one, cutoff)
    compression = basis.T @ operator @ basis
    compression = (compression + compression.T) / 2.0
    distinguished = basis.T @ one
    eigenvalues, eigenvectors = np.linalg.eigh(compression)
    coordinates = eigenvectors.T @ distinguished

    full_moment = matrix_power_moments(operator, one, 2 * m)
    atom_moment = [
        float(np.sum(coordinates**2 * eigenvalues**degree))
        for degree in range(2 * m + 1)
    ]

    projection = np.outer(distinguished, distinguished)
    product = (projection + a * compression) @ (projection - b * compression)
    matrix_lhs = np.trace(np.linalg.matrix_power(product, m))
    matrix_lhs += np.trace(np.linalg.matrix_power(compression, 2 * m))

    alternating = np.trace(np.linalg.matrix_power(red @ blue, m))
    centered_cycle = np.trace(np.linalg.matrix_power(centered_op, 2 * m))
    graphon_lhs = (alternating + centered_cycle) / (p * q) ** m

    epsilon = color_pattern(a, b, m)
    _, coeff = alpha_c(epsilon, full_moment)
    universal = sum(
        value * full_moment[left + right]
        for (left, right), value in coeff.items()
        if value != 0.0
    )

    beta = [density_beta(eigenvalues, coordinates, delta, n) for n in range(10)]
    beta_drop = max(beta[n + 1] - beta[n] for n in range(len(beta) - 1))
    beta_negative = max(0.0, -min(beta))

    mu2 = full_moment[2]
    mu3 = full_moment[3]
    head = 2.0 * mu2 - delta * mu3
    normalized_red = sqrt_weight @ (graphon / p) @ sqrt_weight
    normalized_blue = sqrt_weight @ ((1.0 - graphon) / q) @ sqrt_weight
    rbr = one @ normalized_red @ normalized_blue @ normalized_red @ one
    brb = one @ normalized_blue @ normalized_red @ normalized_blue @ one
    cubic_slack = q * rbr + p * brb

    square_budget = float(np.sum(weights[:, None] * normalized**2 * weights[None, :]))

    return {
        "density_error": abs(float(np.sum(weights[:, None] * graphon * weights[None, :])) - p),
        "moment_error": max(abs(x - y) for x, y in zip(full_moment, atom_moment)),
        "unit_error": abs(float(distinguished @ distinguished) - 1.0),
        "mean_error": abs(full_moment[1]),
        "square_budget": square_budget,
        "compression_budget": float(np.trace(compression @ compression)),
        "head": head,
        "cubic_identity_error": abs(cubic_slack - (1.0 - head)),
        "cubic_slack": cubic_slack,
        "beta_zero_error": abs(beta[0] - 1.0),
        "beta_drop": beta_drop,
        "beta_negative": beta_negative,
        "matrix_graphon_error": abs(matrix_lhs - graphon_lhs),
        "universal_error": abs(universal - graphon_lhs),
        "matrix_lhs": float(matrix_lhs),
        "graphon_lhs": float(graphon_lhs),
        "profile_slack": float((p * q) ** m - alternating),
    }


def even_parity_counterexample(m):
    """Return the normalized alternating density of the balanced bipartite graphon."""
    graphon = np.array([[0.0, 1.0], [1.0, 0.0]])
    sqrt_weight = np.eye(2) / np.sqrt(2.0)
    red = sqrt_weight @ graphon @ sqrt_weight
    blue = sqrt_weight @ (1.0 - graphon) @ sqrt_weight
    alternating = np.trace(np.linalg.matrix_power(red @ blue, m))
    return alternating / (0.25**m)


def run_regressions():
    lower, upper = central_endpoints()
    densities = [lower, 0.35, 0.5, 0.65, upper]
    records = []
    for p in densities:
        for m in (3, 5, 7, 9):
            records.append(graphon_test(p, m, seed=round(1000 * p) + m))

    maxima = {
        key: max(record[key] for record in records)
        for key in (
            "density_error",
            "moment_error",
            "unit_error",
            "mean_error",
            "cubic_identity_error",
            "beta_zero_error",
            "beta_drop",
            "beta_negative",
            "matrix_graphon_error",
            "universal_error",
        )
    }
    maxima["square_budget_excess"] = max(record["square_budget"] - 1.0 for record in records)
    maxima["compression_budget_excess"] = max(
        record["compression_budget"] - 1.0 for record in records
    )
    maxima["head_excess"] = max(record["head"] - 1.0 for record in records)
    maxima["main_excess"] = max(record["graphon_lhs"] - 1.0 for record in records)
    maxima["negative_profile_slack"] = max(-record["profile_slack"] for record in records)
    maxima["even_m_normalized_alt"] = even_parity_counterexample(4)

    for key, value in maxima.items():
        if key == "even_m_normalized_alt":
            assert abs(value - 2.0) < TOL
        else:
            assert value < TOL, (key, value)
    return maxima


if __name__ == "__main__":
    print("Fixed-density Krylov regressions")
    for name, value in run_regressions().items():
        print(f"  {name:30s} {value:.3e}")
