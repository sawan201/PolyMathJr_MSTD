from itertools import combinations
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
from math import comb
from collections import Counter

'''
To run: 
1) Make sure you have python installed on your local machine
2) Create a new file ending in "___.py" and copy everything here as it is in your local file, or simply download this one
3) Go down to where it says histogram_plot(q, k, h), and simply set values for q, k, and h as you please
4) If you are using an editor like VsCode, simply click the run button on the top right. Otherwise you will need to use the terminal. Refer online for instructions
on how to do so on your local Machine and OS. 
'''

'''
For q >> h this code will be computationally costly, but in my second commit I have tried to lower memory cost by negating usage of subset(q,k) thereby not having to store subset(q,k) twice.
Instead it will be computed, frequency counted, and then discarded.
'''

#Create the set of all k-element subsets of [q]

#in the new commit this function is now obsolete, but still left here in case anyone wants to use it
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
    if q is None or k is None or h is None:
        raise ValueError("q, k, and h cannot be None")

    if q < k:
        raise ValueError("q cannot be less than k")

    if k < 1:
        raise ValueError("k cannot be less than 1")

    if h < 1:
        raise ValueError("h cannot be less than 1")

    frequency_by_size = Counter()

    
    for A in combinations(range(1, q + 1), k):
        hA = iterated_sumset(A, h)
        size = len(hA)

        frequency_by_size[size] += 1

    return frequency_by_size

# Function to plot the sizes hA and their frequencies
def histogram_plot(q, k, h, save_as=None):
    frequency_by_size = run(q, k, h)

    if len(frequency_by_size) == 0:
        raise ValueError("There is no data to plot")

    minimum_size = min(frequency_by_size)
    maximum_observed = max(frequency_by_size)

    #k-element subsets of [q]
    bigQ = comb(q,k)

    # Unrestricted theoretical maximum.
    M_hk = comb(h + k - 1, k - 1)

    # Include M_hk on the graph even if its frequency is zero.
    maximum_plotted = max(maximum_observed, M_hk)

    sizes = list(range(minimum_size, maximum_plotted + 1))

    frequencies = [
        frequency_by_size.get(size, 0)
        for size in sizes
    ]

    fig, ax = plt.subplots(figsize=(10, 6))

    bars = ax.bar(
        sizes,
        frequencies,
        width=0.9,
        color="steelblue",
        edgecolor="black"
    )

    ax.set_xticks(sizes)
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))

    ax.set_xlabel(r"Size $|hA|$")
    ax.set_ylabel(r"Number of sets $A$")
    ax.set_title(
        f"Distribution of |{h}A| over "
        f"{k}-element subsets of [{q}]"
    )

    # Write each nonzero frequency above its bar.
    for frequency, bar in zip(frequencies, bars):
        if frequency > 0:
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                frequency,
                str(frequency),
                ha="center",
                va="bottom"
            )

    fig.text(
        0.5,
        0.02,
        rf"Unrestricted maximum: $M_{{{h},{k}}}={M_hk}$"
        rf"   |   Maximum attained in $[{q}]$: "
        rf"${maximum_observed}$"
        rf" |   #${k}$-element subsets of $[{q}]$: ${bigQ}$",
        ha="center",
        va="bottom",
        fontsize=11
    )

    fig.tight_layout(rect=[0, 0.08, 1, 1])

    if save_as is not None:
        fig.savefig(save_as, dpi=300, bbox_inches="tight")

    plt.show()

    return fig, ax


# histogram_plot(q, k, h)
histogram_plot(90, 5, 3)


