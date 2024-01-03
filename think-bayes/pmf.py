import empiricaldist as emp
import pandas as pd


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
