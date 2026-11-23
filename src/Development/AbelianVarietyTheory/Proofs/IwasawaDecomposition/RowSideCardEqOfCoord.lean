module

public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

end GlobalTheory
