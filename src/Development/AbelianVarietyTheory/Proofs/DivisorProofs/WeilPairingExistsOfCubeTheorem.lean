module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt GlobalTheory.CartierDual WithConv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilHom

section Alg

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

section Values

variable [Algebra R A] [Algebra R B] {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]

end Values

variable [Bialgebra R A] [Bialgebra R B]

variable [Module.Finite R B] [Module.Projective R B] {u : A ⊗[R] B} (h : IsBimul u)

end Alg

section Geo

variable {S : Scheme.{0}}

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

end Geo

end GlobalTheory.WeilHom
