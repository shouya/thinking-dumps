import numpy as np
from utils import Pmf
from scipy.stats import gaussian_kde

class MCMC:
    def __init__(self, sample_prior, likelihood):
        self.sample_prior = sample_prior
        self.likelihood = likelihood

    def step(self, x, r):
        y = self.sample_prior()
        s = self.likelihood(y)
        if s > r or np.random.rand() < s/r:
            return (y, s)
        return (x, r)
        
    def trace_with_likelihoods(self, n):
        x = self.sample_prior()
        r = self.likelihood(x)
        out = [(x, r)]
        for _ in range(n):
            x, r = self.step(x, r)
            out.append((x, r))
        return out

    def trace(self, n):
        return [x for (x, r) in self.trace_with_likelihoods(n)]

    def iterate(self, n):
        x = self.sample_prior()
        r = self.likelihood(x)
        for _ in range(n):
            x, r = self.step(x, r)
        return (x, r)
        
    def sample(self, n, n_iter):
        return [self.iterate(n_iter)[0] for _ in range(n)]

    def posterior_pmf(self, n, n_iter):
        posterior = Pmf.from_seq(self.sample(n, n_iter))
        return posterior
        
    def posterior_pmf_kde(self, n, n_iter, qs):
        pmf = self.posterior_pmf(n, n_iter)
        kde = gaussian_kde(self.sample(n, n_iter))
        ps = kde.evaluate(qs)
        pmf = Pmf(ps, qs)
        pmf.normalize()
        return pmf

