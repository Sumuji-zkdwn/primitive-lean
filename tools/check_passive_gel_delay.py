"""Passive delayed-gel test: exact energy identity and a finite cubic-graph relaxation.

No gauge fields, gravity equations, localized solitons, or Lorentz invariance are
claimed. SymPy performs polynomial identities; SciPy provides finite checks.
"""
from itertools import product
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp


def symbolic_energy_identity():
    x = sp.Matrix(sp.symbols("x0:3", real=True))
    v = sp.Matrix(sp.symbols("v0:3", real=True))
    h = sp.Matrix(sp.symbols("h0:2", real=True))
    rho, a, b, kappa, gamma = sp.symbols("rho a b kappa gamma", positive=True)
    B = sp.Matrix([[-1, 1, 0], [0, -1, 1]])
    eps = B * x
    delta = eps - h
    drive = delta.applyfunc(lambda z: b * z + kappa * z**3)
    stress = a * eps + drive
    dv = -B.T * stress / rho
    dh = gamma * drive
    energy = rho * v.dot(v) / 2 + a * eps.dot(eps) / 2 + sum(
        b * d**2 / 2 + kappa * d**4 / 4 for d in delta
    )
    dedt = sum(sp.diff(energy, var) * rate for var, rate in zip(
        list(x) + list(v) + list(h), list(v) + list(dv) + list(dh)
    ))
    assert sp.expand(dedt + gamma * drive.dot(drive)) == 0
    print("PASS exact symbolic 3-vertex graph: E_dot = -gamma * sum(drive_e**2)")


def cube_incidence():
    nodes = list(product((0, 1), repeat=3))
    idx = {node: i for i, node in enumerate(nodes)}
    edges = []
    for u, node in enumerate(nodes):
        for axis in range(3):
            if node[axis] == 0:
                nbr = list(node)
                nbr[axis] = 1
                edges.append((u, idx[tuple(nbr)]))
    B = np.zeros((len(edges), len(nodes)))
    for i, (u, v) in enumerate(edges):
        B[i, u] = -1
        B[i, v] = 1
    return B


def numeric_relaxation(kappa):
    B = cube_incidence()
    n, m = B.shape[1], B.shape[0]
    rho, a, b, tau = 1.0, 1.0, 1.0, 0.4
    gamma = 1.0 / (b * tau)
    x0 = np.zeros(n)
    x0[0] = 1.0
    y0 = np.r_[x0, np.zeros(n), np.zeros(m)]

    def rhs(_t, state):
        x, v, h = state[:n], state[n:2*n], state[2*n:]
        eps = B @ x
        delta = eps - h
        drive = b * delta + kappa * delta**3
        stress = a * eps + drive
        return np.r_[v, -B.T @ stress / rho, gamma * drive]

    def energy(state):
        x, v, h = state[:n], state[n:2*n], state[2*n:]
        eps = B @ x
        d = eps - h
        return (rho*v@v + a*eps@eps + b*d@d)/2 + kappa*np.sum(d**4)/4

    result = solve_ivp(rhs, (0, 80), y0, method="DOP853", rtol=1e-10,
                       atol=1e-12, max_step=0.12, dense_output=False,
                       t_eval=np.linspace(0, 80, 801))
    assert result.success, result.message
    vals = np.array([energy(result.y[:, j]) for j in range(result.y.shape[1])])
    assert np.max(np.diff(vals)) < 1e-9, np.max(np.diff(vals))
    assert vals[-1] < 1e-7, vals[-1]
    assert np.std(result.y[:n, -1]) < 2e-4
    assert np.isclose(np.mean(result.y[:n, -1]), 1/n, atol=1e-8)
    print(f"PASS 3D cube (8 sites, 12 edges), kappa={kappa:g}: "
          f"E(0)={vals[0]:.8f}, E(80)={vals[-1]:.3g}, "
          f"x_final_std={np.std(result.y[:n,-1]):.3g}")


def linear_dispersion():
    # Plane-wave ansatz exp(i*k*x - i*omega*t):
    # -i*rho*tau*omega^3 + rho*omega^2 + i*tau*(a+b)*k^2*omega-a*k^2=0.
    rho = a = b = tau = 1.0
    for k in (0.02, 0.04, 0.1, 1.0, 20.0):
        roots = np.roots([-1j*rho*tau, rho, 1j*tau*(a+b)*k*k, -a*k*k])
        assert np.max(roots.imag) < 1e-9, (k, roots)
        positive = max(roots, key=lambda z: z.real)
        if k == 0.02:
            assert abs(positive.real/k - np.sqrt(a/rho)) < 0.001
            assert abs(positive.imag/k**2 + b*tau/(2*rho)) < 0.001
        if k == 20.0:
            assert abs(positive.real/k - np.sqrt((a+b)/rho)) < 0.002
        print(f"PASS dispersion k={k:5.2f}: positive branch omega={positive.real:+.7f}{positive.imag:+.7f}i")


def no_go_connected_graph():
    B = cube_incidence()
    eigs = np.linalg.eigvalsh(B.T @ B)
    assert np.sum(eigs < 1e-10) == 1
    # At equilibrium drive=0 (b,kappa>0) forces h=Bx;
    # then B^T B x=0, and the unique stationary configuration (mod
    # translations) is x constant, i.e., no localized static defect.
    print("PASS finite static no-go: 3D cube graph Laplacian rank=7; only constant x")


if __name__ == "__main__":
    symbolic_energy_identity()
    no_go_connected_graph()
    numeric_relaxation(kappa=0)
    numeric_relaxation(kappa=8)
    linear_dispersion()
