from itertools import combinations
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
from math import comb

'''
To run: 
1) Make sure you have python installed on your local machine
2) Create a new file ending in "___.py" and copy everything here as it is in your local file, or simply download this one
3) Go down to where it says histogram_plot(q, k, h), and simply set values for q, k, and h as you please
4) If you are using an editor like VsCode, simply click the run button on the top right. Otherwise you will need to use the terminal. Refer online for instructions
on how to do so on your local Machine and OS. 
'''

#Create the set of all k-element subsets of [q]
def subset(q, k):
    if q is None or k is None:
        raise ValueError("q and/or k cannot be none")
    if (q < k):
        return set()
    
    q = range(1, q+1)
    subsets = set(combinations(q, k))

    return subsets

# find the cardinality of any input set X
def card(X):
    if X is None:
        return 0
    
    return len(X)

# Generate the sumset A+B for any two sets A,B
def sumset(A, B):
    new_A = set()
    for a in A:
        for b in B:
            new_A.add(a+b)
    return new_A

# Recursively define the h-fold iterated sumset of A
def iterated_sumset(A, h):
    if h < 1:
        raise ValueError("h cannot be less than 1")
    if card(A) == 0:
        raise ValueError("A cannot be empty")
    
    if h == 1:
        return A
    return sumset(A, iterated_sumset(A, h-1))

# Function to record subsets of subset(q, k) and their h-fold iterated sumset cardinality
# deliberately uses dictionaries in case we want to look at what subsets A produce cardinality = |hA|
def run(q, k, h):
    Q = subset(q,k)
    if card(Q) == 0:
        raise ValueError('q cannot be less than k')
    
    size = {}
    for A in Q:
        new_A = iterated_sumset(A, h)
        size[A] = card(new_A)

    return size

# Function to plot the sizes hA and their frequencies
def histogram_plot(q, k, h, save_as=None):
    size_by_set = run(q, k, h)

    if isinstance(size_by_set, Exception):
        raise size_by_set

    sizes = list(size_by_set.values())

    if len(sizes) == 0:
        raise ValueError("There is no data to plot")

    minimum_size = min(sizes)
    maximum_size = max(sizes)

    # Center one bin at each integer.
    bin_edges = [
        n - 0.5
        for n in range(minimum_size, maximum_size + 2)
    ]

    fig, ax = plt.subplots(figsize=(10, 6))

    frequencies, _, bars = ax.hist(
        sizes,
        bins=bin_edges,
        color="steelblue",
        edgecolor="black",
        rwidth=0.9
    )

    # Use only integers on both axes.
    ax.set_xticks(range(minimum_size, maximum_size + 1))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))

    ax.set_xlabel(r"Size $|hA|$")
    ax.set_ylabel(r"Number of sets $A$")
    ax.set_title(
        f"Distribution of |{h}A| over "
        f"{k}-element subsets of [{q}]"
    )

    # Write the frequency above each bar.
    for frequency, bar in zip(frequencies, bars):
        if frequency > 0:
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                frequency,
                str(int(frequency)),
                ha="center",
                va="bottom"
            )

    # The theoretical maximum possible value of |hA|.
    M_hk = comb(h + k - 1, k - 1)

    fig.text(
        0.5,
        0.02,
        rf"Unrestricted maximum: $M_{{{h},{k}}}={M_hk}$"
        rf"   |   Maximum attained in $[{q}]$: ${maximum_size}$",
        ha="center",
        va="bottom",
        fontsize=11
    )

    # Reserve space for the text at the bottom.
    fig.tight_layout(rect=[0, 0.08, 1, 1])

    if save_as is not None:
        fig.savefig(save_as, dpi=300, bbox_inches="tight")

    plt.show()

    return fig, ax

# histogram_plot(q, k, h)
histogram_plot(50, 5, 3)

