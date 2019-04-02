K-theory
========

Author: Daniel R. Grayson <dan@math.uiuc.edu>

In this subdirectory of "CategoryTheory" we formalize the category theory
useful in higher algebraic K-theory, namely Quillen's theory of exact
categories, as developed here:

* Daniel Quillen, Higher algebraic K-theory. I, Algebraic K-theory, I: Higher
  K-theories (Proc. Conf., Battelle Memorial Inst., Seattle, Wash., 1972),
  Springer, Berlin, 1973, pp. 85–147. Lecture Notes in Math., Vol. 341.

We also follow the careful and efficient exposition presented here:

* Bühler, Theo, Exact categories, Expo. Math. 28 (2010), no. 1, 1–69.

Note: it might be nice to work toward definitions of "additive category" and
"abelian category" as properties of a category, rather than as added
structures.  That is the approach of Mac Lane in sections 18, 19, and 21 of
[Duality for
groups](http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045),
Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.

Note: when we show that an exact category can be embedded as a full subcategory
of an abelian category, closed under extensions, that abelian category is
automatically univalent, since it is a functor category to the (univalent)
category of abelian groups, so if we take the essential image of the embedding
(consisting of the representable functors) we get a new exact category that is
univalent and equivalent to the old one.  Of course, we could have just done
that with the category of representable functors to sets.  Is there any
advantage to the additional point of view?

Acknowledgments
===============

I thank the Oswald Veblen Fund and the Bell Companies Fellowship for supporting
my stay at the Institute for Advanced Study in Fall, 2013, and in Spring, 2014,
where I started writing this code.

I thank The Ambrose Monell Foundation for supporting my stay at the Institute
for Advanced Study in Fall, 2015, where I continued working on this code.

I thank the Oswald Veblen Fund and the Friends of the Institute for Advanced
Study for supporting my stay at the Institute for Advanced Study in Spring,
2017, where I continued working on this code.

I thank the Center for Advanced Study of the Norwegian Academy of Science and
Letters, for its support for this work was done as part of the project
"Homotopy Type Theory and Univalent Foundations", October-March, 2018-19.
See <https://cas.oslo.no/research-groups/homotopy-type-theory-and-univalent-foundations-article2083-827.html>.
