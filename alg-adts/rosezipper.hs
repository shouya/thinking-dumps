
data Rose a = Rose a [Rose a]

{-
R(a) = a * L(R(a))

dR(a) = a * dL(R(a)) + L(R(a))    -- differentiate implicitly
dR(a) = a * dL(R) * dR(a) + L(R(a))  -- chain rule
dR(a) = a * L(R)^2 * dR(a) + L(R(a))  -- expand dL(R)
dR(a) * (1 - a*L(R)^2) = L(R(a))
dR(a) = L(R(a)) / (1 - a * L(R)^2)

dR(a) = L(R(a)) * L(a*L(R)^2)  -- apply L(a) = 1/(1-a)

Therefore:

RZ(a) = (a, RZ [R(a)] [(a,([R(a)],[R(a)]))])
-}

data RoseZipper a = RZ a [Rose a] [(a, [R(a)], [R(a)])]

{-

It should look like this.

-}
