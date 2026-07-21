"""
Distribution of |hA| over k-element subsets A of [q] = {1, ..., q},
where hA = A + A + ... + A (h summands).

Modes
-----
"exhaustive" : exact distribution over all C(q, k) subsets. By translation
               invariance only C(q-1, k-1) sumsets are actually evaluated, so this is feasible up to a few million
               evaluations
"sample"     : |hA| for n_samples subsets drawn uniformly at random. Estimates
               the shape of the distribution for any q, k, h
"auto"       : exhaustive when cheap enough (work <= exhaustive_limit),
               otherwise sample.


edit the __main__ block at the bottom and run the file.
"""

from collections import Counter
from itertools import combinations
from math import comb, gcd
import random

import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator

try:                                    # Python >= 3.10
    _popcount = int.bit_count
except AttributeError:                  # fallback for older Pythons
    def _popcount(x):
        return bin(x).count("1")


def h_fold_size(A, h):
    """|hA| for a collection A of integers, h >= 1."""
    if h < 1:
        raise ValueError("h cannot be less than 1")
    a0 = min(A)
    gaps = sorted(a - a0 for a in A)            # gaps[0] == 0
    g = 0
    for x in gaps:
        g = gcd(g, x)
    if g > 1:                                   # dilation invariance
        gaps = [x // g for x in gaps]

    S = 0
    for a in gaps:
        S |= 1 << a
    shifts = gaps[1:]                           # shifting by 0 is a no-op
    for _ in range(h - 1):
        T = S                                   # the a = 0 term
        for a in shifts:
            T |= S << a
        S = T
    return _popcount(S)


def h_fold_set(A, h):
    """The actual set hA for inspecting small cases."""
    if h < 1:
        raise ValueError("h cannot be less than 1")
    S = set(A)
    for _ in range(h - 1):
        S = {s + a for s in S for a in A}
    return S


def exact_distribution(q, k, h, examples=None):
    """Exact Counter {|hA|: number of A} over all C(q, k) k-subsets of [q].

    Enumerates only subsets with min = 1 and weights each by its number of
    translates in [q], which is q - max(A) + 1.
    """
    freq = Counter()
    if k == 1:
        freq[1] = q                             # hA = {h*a} for singletons
        if examples is not None:
            examples[1] = (1,)
        return freq
    for rest in combinations(range(2, q + 1), k - 1):
        s = h_fold_size((1,) + rest, h)
        freq[s] += q - rest[-1] + 1
        if examples is not None and s not in examples:
            examples[s] = (1,) + rest
    return freq


def sampled_distribution(q, k, h, n_samples, seed=None, examples=None):
    """Counter of |hA| over n_samples uniformly random k-subsets of [q]."""
    rng = random.Random(seed)
    population = range(1, q + 1)
    freq = Counter()
    for _ in range(n_samples):
        A = rng.sample(population, k)
        s = h_fold_size(A, h)
        freq[s] += 1
        if examples is not None and s not in examples:
            examples[s] = tuple(sorted(A))
    return freq


def run(q, k, h, mode="auto", n_samples=200_000,
        exhaustive_limit=5_000_000, seed=None):
    """Compute the distribution of |hA|.

    Returns (freq, mode, total, examples):
      freq     Counter {size: count} -- counts of subsets (exhaustive)
               or of samples (sample mode)
      mode     "exhaustive" or "sample", whichever was actually used
      total    C(q, k)
      examples {size: one subset attaining it}, for follow-up inspection
    """
    if q is None or k is None or h is None:
        raise ValueError("q, k, and h cannot be None")
    if k < 1:
        raise ValueError("k cannot be less than 1")
    if q < k:
        raise ValueError("q cannot be less than k")
    if h < 1:
        raise ValueError("h cannot be less than 1")

    total = comb(q, k)
    work = comb(q - 1, k - 1)                   # true exhaustive cost
    if mode == "auto":
        mode = "exhaustive" if work <= exhaustive_limit else "sample"

    examples = {}
    if mode == "exhaustive":
        freq = exact_distribution(q, k, h, examples)
    elif mode == "sample":
        freq = sampled_distribution(q, k, h, n_samples, seed, examples)
    else:
        raise ValueError("mode must be 'auto', 'exhaustive', or 'sample'")
    return freq, mode, total, examples


def _sci(n):
    """8.33e+17 -> mathtext '8.33 \\times 10^{17}'."""
    mant, exp = f"{n:.2e}".split("e")
    return rf"{mant} \times 10^{{{int(exp)}}}"


def histogram_plot(q, k, h, mode="auto", n_samples=200_000,
                   exhaustive_limit=5_000_000, seed=None, save_as=None,
                   top_n=10, log_y=False):
    """Plot the distribution of |hA|.

    top_n : how many of the most frequent sizes are printed to the console
            and, when the size range is too wide to label every bar, become
            the x-ticks (their bars are highlighted in orange).
    log_y : log-scale the y-axis -- useful when one size (usually M_{h,k})
            swallows the whole linear scale.
    """
    freq, mode, total, _ = run(q, k, h, mode, n_samples,
                               exhaustive_limit, seed)
    if not freq:
        raise ValueError("There is no data to plot")

    top = freq.most_common(top_n)               # [(size, count), ...]
    unit = "sets" if mode == "exhaustive" else "samples"
    print(f"top {len(top)} most frequent sizes ({unit}):")
    for s, c in top:
        print(f"  |{h}A| = {s:>5}   {c:,}")

    m_hk = comb(h + k - 1, k - 1)               # unrestricted maximum
    lo = min(freq)
    hi = max(max(freq), m_hk)
    sizes = list(range(lo, hi + 1))
    heights = [freq.get(s, 0) for s in sizes]

    fig, ax = plt.subplots(figsize=(10, 6))
    bars = ax.bar(sizes, heights, width=0.9, color="steelblue",
                  edgecolor="black", linewidth=0.4)
    ax.axvline(m_hk, color="firebrick", linestyle="--", linewidth=1.2,
               label=rf"$M_{{{h},{k}}} = {m_hk}$")
    ax.legend(loc="upper left")

    if len(sizes) <= 30:                        # room to label every bar
        ax.set_xticks(sizes)
        for height, bar in zip(heights, bars):
            if height:
                ax.text(bar.get_x() + bar.get_width() / 2, height,
                        str(height), ha="center", va="bottom", fontsize=8)
    else:                                       # ticks at the top_n sizes
        top_sizes = sorted(s for s, _ in top)
        for s in top_sizes:
            bars[s - lo].set_facecolor("darkorange")
        ax.set_xticks(top_sizes)
        ax.set_xticklabels(top_sizes, rotation=45, ha="right", fontsize=8)

    if log_y:
        ax.set_yscale("log")
    else:
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))

    ax.set_xlabel(r"Size $|hA|$")
    if mode == "exhaustive":
        ax.set_ylabel(r"Number of sets $A$")
        ax.set_title(rf"Distribution of $|{h}A|$ over all "
                     rf"{k}-element subsets of $[{q}]$ (exact)")
        note = (rf"max attained in $[{q}]$: {max(freq)}   |   "
                rf"$C({q},{k}) = {total:,}$ subsets")
    else:
        ax.set_ylabel(r"Number of sampled sets $A$")
        ax.set_title(rf"Distribution of $|{h}A|$ over {n_samples:,} random "
                     rf"{k}-element subsets of $[{q}]$")
        note = (rf"max in sample: {max(freq)}   |   sampled {n_samples:,} "
                rf"of $C({q},{k}) \approx {_sci(total)}$ subsets")
    fig.text(0.5, 0.02, note, ha="center", va="bottom", fontsize=10)
    fig.tight_layout(rect=[0, 0.06, 1, 1])

    if save_as is not None:
        fig.savefig(save_as, dpi=300, bbox_inches="tight")
    plt.show()
    return fig, ax


if __name__ == "__main__":
    # def histogram_plot(q, k, h, mode="auto", n_samples=200_000,
    #                    exhaustive_limit=5_000_000, seed=None, save_as=None,
    #                    top_n=10, log_y=False)
    histogram_plot(10_000, 6, 4, n_samples=200_000, seed=1)
