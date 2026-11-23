module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem isAlgZp_tower_zeta {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : IsAlgZp (p := p) (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
  · simp [(T.prim n).pow_eq_one]

theorem mem_of_fixed_ggeo_gn : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) →
    (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F →
    ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p _ Ω _ _ hc T n F hO hA hq o ho
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  haveI : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  letI : Algebra (O0 p) F := f.toAlgebra
  haveI : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) := fun a b h => hc.inj (congrArg Subtype.val h)
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  haveI : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have key := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) o).2 fun σ => by
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ (isAlgZp_tower_zeta T n)⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := key
  exact x.2

end GlobalTheory.GeoFix
