module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ms_single {B X Y : Type} [CommRing B] [Group X] [Group Y] (f : X →* Y) (a : X) (c : B) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem ms_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a : F.G₀) (c : B) :
    F.star O B n (MonoidAlgebra.single a c) =
      MonoidAlgebra.single (F.conj a)⁻¹ (c * ((F.eps O B a ^ (1 - (n : ℤ)) : Bˣ) : B)) := by
  unfold GFrame.star GFrame.starOp
  rw [MonoidAlgebra.lift_single, MulOpposite.unop_smul]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]

theorem UpperTheory.V.Pa.map_star :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B], (∀ y, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.star O B n y) = G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B g.p₀ y)) ∧ (∀ v (ψ : Fin n → L.Gv v →* Bˣ) a, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.oEl v ψ a) = G'.frame.oEl v ψ a) ∧ (∀ (ph : G.G₀) (U : Fin n → B), MonoidAlgebra.mapDomainRingHom B g.p₀ (q1El ph U) = q1El (g.p₀ ph) U) ∧ ∀ (ph ta : G.G₀) (U : Fin n → B) i y, MonoidAlgebra.mapDomainRingHom B g.p₀ (q2El ph ta U i y) = q2El (g.p₀ ph) (g.p₀ ta) U i y := by
  intro l _ L G G' g n O _ _ B _ _
  refine ⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add a b ha hb =>
      simp only [GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single a c =>
      rw [ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]
  · unfold GFrame.oEl
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one, g.p₀_φ]
  · unfold q1El
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
  · unfold q2El
    rw [map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2
      funext k
      simp only [Function.comp_apply]
      split_ifs
      · exact map_one _
      · simp only [map_sub, ms_single, map_one]
    · simp only [map_sub, ms_single, map_one]
