module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.lift_baseChange_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  first | exact @GlobalTheory.lift_baseChange | exact GlobalTheory.lift_baseChange | (intros; apply GlobalTheory.lift_baseChange <;> assumption)
