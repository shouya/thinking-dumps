
## Some notes on minizing a DFA

This concept is difficult for me to comprehend. I watched the video
back and forth for many times and sought for some papers about it.

Here are my conclusion: *the key idea to minize a DFA is to merge all
indistinguisable state pairs into the representive ones.*

Now the point is, what does it mean, exactly, by *(in)distinguishable*
pairs.


Refering to the materials, the formal definition of distinguishability
is:

![distinguishablity formal definition](//shouya.github.io/thinking-dumps/automata/notes/dist.png)

This formal definition helped me a lot on understanding what is the
importance of distinguishability.


In my own word, to say states `p` and `q` are distinguishable, means that
there exists at least one input `w`, such that, `d(p,w)` and `d(q,w)`
cannot simultaneously reach the same state `r`. I would understand
this `w` as something like a "distinguisher" that distinguishes `p`
and `q`. Conversely, to say that states `p` and `q` are
indistinguishable, or equivalent, there does not exists any
"distinguisher"'s, which means, they always transfer to the the same
states on all possible inputs.

There is another important concepts about distinguishability. That is,
the inductive rules for distinguishability. Let me make this clear.

The property of distinguishability of states follows the induction
rule. That is, firstly, all accepting states are distinguishable from
all other non-accepting states, because in DFA, accepting states take
eat an input of &epsilon; to an accepting state, which is obviously
not equivalent to any non-accepting states. Secondly, if we say two
states `p` and `q` are distinguishable, and for any input `w`,
`d(r,w) = p` and `d(s,w) = p`. We will say `r` and `s` are also
distinguishable.






## References

* [Jeff's Slide about Decision Properties of Regular Languages](http://infolab.stanford.edu/~ullman/ialc/spr10/slides/rs1.pdf)
* [Jeff's Lectures for CS154, Winter 2000, Lecture 5](http://infolab.stanford.edu/~ullman/ialc/slides/slides5.pdf)
* [Minimization of Finite Automata - Informatik](http://www.informatik.uni-bremen.de/agbs/lehre/ss05/pi2/hintergrund/minimize_dfa.pdf)
