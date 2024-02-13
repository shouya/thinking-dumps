import empiricaldist as emp
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import gaussian_kde

# my monkey patches on the empiricaldist.Pmf class
class Pmf(emp.Pmf):
    # the bind operator is a better version of the "mix" function
    # described in the book. I found it vastly easier to reasonable
    # about in terms of Monadic bind operator.
    def bind(self, f):
        pmfs = [f(q) for q in self.qs]
        df = pd.concat(pmfs, axis=1).fillna(0) * self.ps
        return Pmf(df.sum(axis=1))

    # I'd like to plot the legend whenever a label is specified.
    def plot(self, *args, **kwargs):
        if "label" in kwargs and "legend" not in kwargs:
            kwargs["legend"] = True
        return super().plot(*args, **kwargs)

    # this is how i think Bayes' Theorem should be expressed
    def bayes(self, f):
        likelihoods = [f(q) for q in self.qs]
        return Pmf(self * likelihoods)

    # the Applicative operator:
    # Pmf a -> Pmf b -> ((a,b) -> c) -> Pmf c
    def comb(self, pmf, f):
        out = Pmf()
        for q1, p1 in self.items():
            for q2, p2 in pmf.items():
                out[f(q1, p1)] += p1 * p2
        out.normalize()
        return out

    # the functor map operator
    # Pmf a -> (a -> b) -> Pmf b
    def map(self, f):
        new_qs = [f(q) for q in self.qs]
        return Pmf(self.ps, new_qs)


def make_joint(pmf1, pmf2):
    X, Y = np.meshgrid(pmf1, pmf2)
    return pd.DataFrame(X * Y, columns=pmf1.qs, index=pmf2.qs)

def marginal(joint, axis):
    return Pmf(joint.sum(axis=axis))

def plot_joint(joint, cmap='Blues', **kwargs):
    """Plot a joint distribution with a color mesh."""
    vmax = joint.to_numpy().max() * 1.1
    plt.pcolormesh(joint.columns, joint.index, joint,
        cmap=cmap,
        vmax=vmax,
        shading='nearest',
        **kwargs
    )
    plt.colorbar()

def plot_contour(joint, **kwargs):
    """Plot a joint distribution with a contour."""
    plt.contour(joint.columns, joint.index, joint, linewidths=2, **kwargs)

def normalize_joint(joint):
    """Normalize a joint distribution."""
    prob_data = joint.to_numpy().sum()
    joint /= prob_data
    return joint

def normalize_pmf(pmf):
    pmf.normalize()
    return pmf

def kde_from_samples(samples, qs):
    kde = gaussian_kde(samples)
    ps = kde.evaluate(qs)
    pmf = Pmf(ps, qs)
    pmf.normalize()
    return pmf

def kde_from_pmf(pmf, n=101):
    """Make a kernel density estimate for a PMF."""
    kde = gaussian_kde(pmf.qs, weights=pmf.ps)
    qs = np.linspace(pmf.qs.min(), pmf.qs.max(), n)
    ps = kde.evaluate(qs)
    pmf = Pmf(ps, qs)
    pmf.normalize()
    return pmf