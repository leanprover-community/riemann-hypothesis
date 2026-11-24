module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.HodgeTateFromSandwich
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowMonoTors
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas
public import Mathlib.Data.ZMod.Units
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall
import Mathlib.Tactic.TypeStar
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Order.CompletePartialOrder

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.HodgeTateFromSandwich\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul2 {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (a : ℤ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] (a • y) = (c * algebraMap ℤ_[l] ℚ_[l] a) • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, ← algebraMap_smul ℚ_[l] a, smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

theorem gen_smul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℤ_[l]) : c • (0 : N) = 0 := smul_zero c

theorem gen_baseChange {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N']
    (f : N →ₗ[ℤ_[l]] N') (y : N) : f.baseChange ℚ_[l] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] f y :=
  LinearMap.baseChange_tmul _ _ _

theorem gen_sum_smul {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N'] {r : ℕ}
    (a : Fin r → ℤ_[l]) (e : Fin r → N) (f : N →ₗ[ℤ_[l]] N') (t : Fin r) (g : N') (h1 : f (e t) = g)
    (h2 : ∀ s, s ≠ t → f (e s) = 0) : f (∑ s, a s • e s) = a t • g := by

  rw [map_sum, Finset.sum_eq_single t (fun s _ hs => by rw [map_smul, h2 s hs, smul_zero])
  (fun h => absurd (Finset.mem_univ t) h), map_smul, h1]

theorem gen_span (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] (Set.range fun s => M.toV n (extS l hI j hj _ 0 s (gen s))) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  choose a ha using fun s => hgen s (pullHl l (sch.map (j s)) n 0 x)
  have hx : x = ∑ s, a s • extS l hI j hj _ 0 s (gen s) := by
    refine sum_eq l hI j hj _ 0 _ _ fun t => ?_
    rw [ha t]
    exact (gen_sum_smul a _ _ t _ (extS_self l hI j hj _ 0 t (gen t))
      (fun s hs => extS_ne l hI j hj _ 0 s (gen s) (Ne.symm hs))).symm
  rw [hx, tmul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [gen_tmul_smul2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

theorem gal_step (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (c : ℤ_[l]),
      pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ))) n 0
        (extS l hI j hj _ 0 s (gen s)) = c • extS l hI j hj _ 0 s' (gen s') := by
  obtain ⟨σ, θ, hθ⟩ := htrans s' s
  obtain ⟨π, θ', hθ'⟩ := hperm σ
  have hπ : π s' = s := by
    have := hint s'
    obtain ⟨y⟩ := (inferInstance : Nonempty (Y s'))
    by_contra hne
    have e1 := congrArg (fun f : Y s' ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q => f y) (hθ.symm.trans (hθ' s'))
    simp only [Scheme.Hom.comp_apply] at e1
    exact Set.disjoint_left.1 (hj.2.2 s (π s') (Ne.symm hne)) ⟨_, rfl⟩ ⟨_, e1.symm⟩
  obtain ⟨c, hc⟩ := hgen s' (pullHl l (sch.map θ) n 0 (gen s))
  refine ⟨σ, c, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [← pull_comp_apply, ← Functor.map_comp]
  obtain rfl | ht := eq_or_ne t s'
  · rw [hθ, Functor.map_comp, pull_comp_apply, extS_self, hc, LinearMap.map_smul, extS_self]
  · have hne : π t ≠ s := fun h => ht (π.injective (h.trans hπ.symm))
    rw [hθ' t, Functor.map_comp, pull_comp_apply, extS_ne l hI j hj _ 0 s _ hne, map_zero, LinearMap.map_smul,
      extS_ne l hI j hj _ 0 _ _ ht]
    exact (gen_smul_zero (N := Hl l (sch.obj (Y t)) n 0) c).symm

end CrystallineSemistableComparison.AdicCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowMonoTors\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
  (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (i j' : ℕ)
  (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s)

theorem gsmul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) : a • (0 : N) = 0 := smul_zero a

include hgen in
theorem phi_form (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) (x : M.T i) :
    ∃ a : ℤ_[l], cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y') =
      a • extS l hI j hj _ 0 s (gen s) := by
  obtain ⟨a, ha⟩ := hgen s (pullHl l (sch.map (j s)) _ 0
    (cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y')))
  refine ⟨a, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [LinearMap.map_smul]
  by_cases ht : t = s
  · subst ht
    rw [ha, extS_self]
  · rw [pull_cupL, extS_ne l hI j hj j' 0 s y' ht, cupL_zero_right, extS_ne l hI j hj _ 0 s (gen s) ht]
    exact (gsmul_zero (N := Hl l (sch.obj (Y t)) ((i + j' : ℕ) : ℤ) 0) a).symm

include hgen in
theorem f_exists (s : Fin r) (y' : Hl l (sch.obj (Y s)) j' 0) :
    ∃ f : Module.Dual ℚ_[l] (M.V i), ∀ x : M.T i, ∃ z, M.CupT x (extS l hI j hj j' 0 s y') z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) := by
  set g := M.toV (i + j') (extS l hI j hj _ 0 s (gen s)) with hgdef
  have hz : ∀ x : M.T i, ∃ a : ℤ_[l], M.toV (i + j') (cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y')) =
      algebraMap ℤ_[l] ℚ_[l] a • g := fun x => by
    obtain ⟨a, ha⟩ := phi_form hI M j hj i j' gen hgen s y' x
    exact ⟨a, by rw [ha]; exact toV_smul M (i + j') a _⟩
  by_cases hg0 : g = 0
  · refine ⟨0, fun x => ⟨cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
    obtain ⟨a, ha⟩ := hz x
    rw [ha, hg0, smul_zero, smul_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℚ_[l] (M.V (i + j')), ψ g ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℚ_[l] g).1 hne)
  let Φ : Hl l M.spc (i : ℤ) 0 →ₗ[ℤ_[l]] Hl l M.spc ((i + j' : ℕ) : ℤ) 0 :=
    cupR l hI (Int.ofNat_add_ofNat i j') (add_zero 0) (extS l hI j hj j' 0 s y')
  refine ⟨(ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l]), fun x => ⟨cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y'), fun k => rfl, ?_⟩⟩
  obtain ⟨a, ha⟩ := hz x
  have e1 : (Φ.baseChange ℚ_[l]) (M.toV i x) = M.toV (i + j') (Φ x) := LinearMap.baseChange_tmul _ _ _
  have e2 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = algebraMap ℤ_[l] ℚ_[l] a := by
    have h3 : ((ψ g)⁻¹ • (ψ ∘ₗ Φ.baseChange ℚ_[l])) (M.toV i x) = (ψ g)⁻¹ * ψ (algebraMap ℤ_[l] ℚ_[l] a • g) := by
      change (ψ g)⁻¹ * ψ ((Φ.baseChange ℚ_[l]) (M.toV i x)) = _
      exact congrArg (fun w => (ψ g)⁻¹ * ψ w) (e1.trans ha)
    rw [h3, map_smul, smul_eq_mul, ← mul_assoc, mul_comm _ (algebraMap ℤ_[l] ℚ_[l] a), mul_assoc, inv_mul_cancel₀ hψ,
      mul_one]
  exact ha.trans (congrArg (· • g) e2.symm)

end

theorem dual_span (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (i j' : ℕ) (hij : i + j' = 2 * d) (gen : ∀ s, Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V i) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T i, ∃ z, M.CupT x y z ∧
        M.toV (i + j') z = f (M.toV i x) • M.toV (i + j') (extS l hI j hj _ 0 s (gen s))} = ⊤ := by
  have := fin_of hI M hM i
  refine Adic.span_dual _ fun v hv => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc0 : c = 0
  · rw [hc0, zero_tmul]
  have hN : ((i + j' : ℕ) : ℤ) = 2 * (d : ℤ) := by exact_mod_cast hij
  obtain ⟨e, he⟩ := tors_of_restr l hI j hj (i : ℤ) 0 x fun s => by
    have := hint s
    obtain ⟨hp, hs⟩ := AdicGeo.comp_str hM hc j hj s
    refine hl_nondeg l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (j' : ℤ) _ (Int.ofNat_add_ofNat i j') hN _ fun y' => ?_
    obtain ⟨f, hf⟩ := f_exists hI M j hj i j' gen hgen s y'
    have h0 := hv f ⟨s, _, hf⟩
    rw [tmul_eq_smul_toV M i c x, LinearMap.map_smul, smul_eq_mul, mul_eq_zero] at h0
    have h0' := h0.resolve_left hc0
    obtain ⟨z, hz, hzv⟩ := hf x
    rw [h0', zero_smul] at hzv
    obtain ⟨n, hn⟩ := (Adic.tmul_eq_zero (M := Hl l M.spc ((i + j' : ℕ) : ℤ) 0) z).1 hzv
    have hz' : z = cupL l hI (Int.ofNat_add_ofNat i j') (add_zero 0) x (extS l hI j hj j' 0 s y') := Subtype.ext (funext hz)
    refine ⟨n, ?_⟩
    rw [← extS_self l hI j hj j' 0 s y', ← pull_cupL, ← LinearMap.map_smul, ← hz', hn, map_zero]
  exact tmul_zero_of c x he

end CrystallineSemistableComparison.AdicCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupLZeroRight\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowMonoTors\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gal_of (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (z : ℚ_[l]), z ≠ 0 ∧
      M.act n σ (M.toV n (extS l hI j hj _ 0 s (gen s))) = z • M.toV n (extS l hI j hj _ 0 s' (gen s')) := by
  obtain ⟨σ, c, hc⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s s'
  obtain ⟨σ2, c2, hc2⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s' s
  have hact : ∀ (τ : K.fixingSubgroup) (x : M.T n), M.act n τ (M.toV n x) =
      M.toV n (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K τ))) n 0 x) :=
    fun τ x => gen_baseChange (N := Hl l M.spc n 0) _ x
  by_cases h0 : c = 0
  · have es : extS l hI j hj _ 0 s (gen s) = 0 := pull_gal_inj M n _ _ (by rw [hc, h0]; exact zero_smul _ _)
    have es' : extS l hI j hj _ 0 s' (gen s') = 0 := pull_gal_inj M n _ _ (by rw [hc2, es]; exact gen_smul_zero _)
    refine ⟨σ, 1, one_ne_zero, ?_⟩
    rw [hact, hc, h0, es', one_smul]
    exact congrArg (M.toV n) (zero_smul _ _)
  · refine ⟨σ, algebraMap ℤ_[l] ℚ_[l] c, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 h0
    · rw [hact, hc, toV_smul]

theorem dual_of (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) (hg : M.Geo) : M.Dual d := by
  obtain ⟨r, Y, j, hj, hint, hperm, htrans⟩ := hg
  refine ⟨fun i hi => ?_, fun i j' hij => ?_⟩
  · have hs : ∀ x : M.T i, x = 0 := fun x => sum_inj l hI j hj i 0 x fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact (hl_vanish l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (by exact_mod_cast hi)).elim _ _
    refine ⟨fun v w => ?_⟩
    obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
    obtain ⟨c', x', rfl⟩ := Adic.tmul_surj w
    rw [hs x, hs x', tmul_zero, tmul_zero]
  · have hgen : ∀ s, ∃ g : Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0, ∀ x, ∃ c : ℤ_[l], x = c • g := fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact hl_cyclic l hI (j s ≫ AdicGeo.str M) d _ (by push_cast; exact_mod_cast hij)
    choose gen hgen using hgen
    exact ⟨r, fun s => M.toV (i + j') (extS l hI j hj _ 0 s (gen s)), gen_span hI M j hj _ gen hgen,
      fun s s' => gal_of hI M j hj hint hperm htrans _ gen hgen s s',
      dual_span hI M hM d hc j hj hint i j' hij gen hgen⟩

end CrystallineSemistableComparison.AdicCoh

namespace CrystallineSemistableComparison

theorem adic : LAdicCoefficientPassage := by
  intro hI l _ K G hG hC hGeo
  exact { cup_ex := fun M _ _ x y => AdicCoh.cup_ex hI M x y
          fin := fun M hM j => AdicCoh.fin_of hI M (hG M hM) j
          dual := fun M hM d hc => AdicCoh.dual_of hI M (hG M hM) d hc (hGeo M hM d hc)
          comp := fun M hM => AdicCoh.comp_of hI G hG hC M hM }

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc\nimport Mathlib.Algebra.Category.ModuleCat.FilteredColimits\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSec

open GlobalTheory.EtC

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  change (F.obj.map (k ≫ g).op).hom y = (F.obj.map k.op).hom ((F.obj.map g.op).hom y)
  rw [op_comp, Functor.map_comp]
  rfl

theorem loc_bind' {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h' V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

theorem tw_loc (hG : E.InGen) (Q : ℕ) [NeZero Q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw Q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  have hsurj : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ GlobalTheory.EtC.twF Q i)) y ∈ Scheme.etaleTopology U :=
    Presheaf.imageSieve_mem Scheme.etaleTopology _ (U := op U) y
  refine loc_bind' ⟨_, hsurj, fun V g hg => hg⟩ ?_
  rintro V g ⟨t, ht⟩
  by_cases hP : Nonempty (Prim Q Γ(V, ⊤))
  · obtain ⟨ζ₀⟩ := hP
    obtain ⟨S, hS, hS'⟩ := (hG Q i).1 V ζ₀ (Sec.res g y)
    refine ⟨S, hS, fun W k hk => Or.inr ?_⟩
    obtain ⟨c, hc⟩ := hS' W k hk
    exact ⟨ζ₀.map k.appTop.hom, c, (res_comp k g y).trans hc⟩
  · have : IsEmpty (Prim Q Γ(V, ⊤)) := not_nonempty_iff.mp hP
    have ht0 : t = 0 := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel Q i Γ(V, ⊤))
        (show (Prim Q Γ(V, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(V, ⊤) from t)
      have hf : f = 0 := Finsupp.ext fun a => (IsEmpty.false a).elim
      rw [hf]
      exact Submodule.Quotient.mk_zero _
    have hy : Sec.res g y = 0 := by
      refine ht.symm.trans ?_
      rw [ht0]
      exact map_zero _
    refine ⟨⊤, Scheme.etaleTopology.top_mem V, fun W k _ => Or.inl ?_⟩
    rw [res_comp, hy]
    exact map_zero _

end CrystallineSemistableComparison.TwSec
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.EffectiveEpi.Comp\nimport Mathlib.CategoryTheory.ExtremalEpi\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.Etale.StandardEtale\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem comap_surj_of_lift {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : A →+* K), ∃ χ : S →+* K, χ.comp (algebraMap A S) = ψ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A S)) := by
  intro p
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let ψ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  obtain ⟨χ, hχ⟩ := h K ψ
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change χ (algebraMap A S a) = 0 ↔ a ∈ p.asIdeal
  rw [← RingHom.comp_apply, hχ]
  simp only [ψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField K).injective]
  rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

theorem etaleCover (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S))) :
    ∃ (W : Scheme.{0}) (π : W ⟶ U) (φ : S →+* Γ(W, ⊤)),
      Sieve.ofArrows (fun _ : Unit => W) (fun _ => π) ∈ Scheme.etaleTopology U ∧
      ∀ a, φ (algebraMap Γ(U, ⊤) S a) = π.appTop.hom a := by
  let φ0 : Γ(U, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)
  have : Etale (Spec.map φ0) := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map φ0) := ⟨hS⟩
  have : Surjective (pullback.fst U.toSpecΓ (Spec.map φ0)) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  refine ⟨pullback U.toSpecΓ (Spec.map φ0), pullback.fst _ _,
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop).hom, ?_, ?_⟩
  · let 𝒰 : U.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Unit
      (fun _ => pullback U.toSpecΓ (Spec.map φ0)) (fun _ => pullback.fst _ _)
      (fun x => ⟨(), (pullback.fst U.toSpecΓ (Spec.map φ0)).surjective x⟩) (fun _ => inferInstance)
    exact 𝒰.mem_grothendieckTopology
  · intro a
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := U.toSpecΓ) (g := Spec.map φ0))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
    have key : φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop =
        (pullback.fst U.toSpecΓ (Spec.map φ0)).appTop := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h, ← Category.assoc, ← Scheme.ΓSpecIso_naturality]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k => k.hom a) key

theorem loc_of_etale (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S)))
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (χ : S →+* Γ(V, ⊤)), (∀ a, χ (algebraMap Γ(U, ⊤) S a) = g.appTop.hom a) → P V g) :
    Loc U P := by
  obtain ⟨W, π, φ, hmem, hφ⟩ := etaleCover U S hS
  refine ⟨_, hmem, fun V g hg => ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  refine hP V (h ≫ π) (h.appTop.hom.comp φ) fun a => ?_
  rw [RingHom.comp_apply, hφ, Scheme.Hom.comp_appTop]
  rfl

theorem kumLoc (U : Scheme.{0}) (m : ℕ) (u : (Γ(U, ⊤))ˣ) (hm : IsUnit (m : Γ(U, ⊤))) :
    Loc U fun V g => ∃ v : Γ(V, ⊤), v ^ m = g.appTop.hom u.1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨1, ?_⟩⟩
    have h01 : (0 : Γ(U, ⊤)) = 1 := by simpa using isUnit_zero_iff.mp (by simpa using hm)
    have h01' : (0 : Γ(V, ⊤)) = 1 := by simpa using congrArg g.appTop.hom h01
    have := subsingleton_of_zero_eq_one h01'
    exact Subsingleton.elim _ _
  · let c : Γ(U, ⊤) := (hm.unit⁻¹ : (Γ(U, ⊤))ˣ)
    have hc : c * (m : Γ(U, ⊤)) = 1 := hm.val_inv_mul
    let Pp : StandardEtalePair Γ(U, ⊤) :=
      { f := X ^ m - C u.1
        monic_f := monic_X_pow_sub_C _ hm0.ne'
        g := X
        cond := ⟨C c * X, 0, m, by
          rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
          have hX : (X : (Γ(U, ⊤))[X]) ^ (m - 1) * X = X ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
          have hC : C (m : Γ(U, ⊤)) * C c = 1 := by rw [← C_mul, mul_comm, hc, C_1]
          linear_combination (X ^ (m - 1) * X) * hC + hX⟩ }
    refine loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_
    · obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ψ u.1) hm0
      let _ := ψ.toAlgebra
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_pow hm0.ne'] at hx
        exact (u.isUnit.map ψ).ne_zero hx.symm
      have hmap : Pp.HasMap x := ⟨by simp [Pp, hx, RingHom.algebraMap_toAlgebra], by simpa [Pp] using hx0⟩
      exact ⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩
    · refine ⟨χ Pp.X, ?_⟩
      have h0 := (StandardEtalePair.hasMap_X (P := Pp)).1
      have h1 : Pp.X ^ m = algebraMap Γ(U, ⊤) Pp.Ring u.1 := by
        simpa [Pp, sub_eq_zero] using h0
      rw [← map_pow, h1, hχ]

end CrystallineSemistableComparison.KummerTwistLemmas
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem cyc_pow (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∀ a : ℕ, expand ℤ (p ^ a) (cyclotomic (p ^ b) ℤ) = cyclotomic (p ^ (a + b)) ℤ
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ', expand_mul, cyc_pow p b hp hb a,
      cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (by omega : a + b ≠ 0))]
    congr 1
    rw [← pow_succ]
    congr 1
    omega

theorem rootLoc (p a b : ℕ) [Fact p.Prime] (hb : 0 < b) (U : Scheme.{0}) (ξ : Prim (p ^ b) Γ(U, ⊤)) :
    Loc U fun V g => ∃ ζ : Prim (p ^ (a + b)) Γ(V, ⊤), ζ.1 ^ (p ^ a) = g.appTop.hom ξ.1 := by
  have hp : p.Prime := Fact.out
  have hpU : IsUnit (p : Γ(U, ⊤)) := by
    have h := ξ.2.1
    rw [Nat.cast_pow] at h
    exact (isUnit_pow_iff hb.ne').1 h
  have hξ1 : ξ.1 ^ (p ^ b) = 1 := by
    obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one (p ^ b) ℤ
    have := congrArg (aeval ξ.1) hh
    rw [map_mul, ξ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hξu : IsUnit ξ.1 := by
    refine isUnit_iff_exists_inv.2 ⟨ξ.1 ^ (p ^ b - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)), hξ1]
  obtain ⟨S, hS, hP⟩ := kumLoc U (p ^ a) hξu.unit (by rw [Nat.cast_pow]; exact hpU.pow _)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, hv⟩ := hP V g hg
  rw [IsUnit.unit_spec] at hv
  have hpV : IsUnit (p : Γ(V, ⊤)) := by simpa using hpU.map g.appTop.hom
  refine ⟨⟨v, by rw [Nat.cast_pow]; exact hpV.pow _, ?_⟩, hv⟩
  rw [← cyc_pow p b hp hb a, expand_aeval, hv]
  exact (Prim.map g.appTop.hom ξ).2.2

end CrystallineSemistableComparison.KummerTwistLemmas
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.SheafSectionLemmas

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hSP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  refine ⟨Sieve.bind S.arrows (fun V g hg => (h' V g (hSP V g hg)).choose),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => (h' V g (hSP V g hg)).choose_spec.1), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hSP V g hg)).choose_spec.2 W k hk

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ((isSheaf_types F) S hS).isSeparatedFor.ext fun _ g hg => hSP _ g hg

theorem sec_subsingleton_of_isEmpty (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ⟨fun a b => ((isSheaf_types F).isSheafFor (⊥ : Presieve U)
    (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology U)).isSeparatedFor.ext (fun _ _ h => h.elim)⟩

theorem epi_of_loc {F G : Shv R} (φ : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec G U), Loc U fun V g => ∃ x : Sec F V, Sec.map φ x = Sec.res g y) : Epi φ := by
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro U y
    obtain ⟨S, hS, hSP⟩ := h U y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hSP V g hg
    exact ⟨x, hx⟩
  infer_instance

theorem sec_map_comp {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_injective_of_mono {X Y : Shv R} (f : X ⟶ Y) [Mono f] (U : Scheme.{0}) :
    Function.Injective (Sec.map f (U := U)) := by
  have h1 : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have h2 : Mono (f.hom.app (op U)) := (NatTrans.mono_iff_mono_app f.hom).1 h1 (op U)
  exact (ModuleCat.mono_iff_injective _).1 h2

theorem epi_lift_of_loc {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ (U : Scheme.{0}) (y : Sec Y U), Sec.map g y = 0 →
      Loc U fun V k => ∃ x : Sec X V, Sec.map f x = Sec.res k y) :
    Epi (kernel.lift g f w) := by
  apply epi_of_loc
  intro U y
  have hy : Sec.map g (Sec.map (kernel.ι g) y) = 0 := by
    rw [← sec_map_comp, kernel.condition]; rfl
  refine loc_mono (h U _ hy) fun V k ⟨x, hx⟩ => ⟨x, ?_⟩
  apply sec_map_injective_of_mono (kernel.ι g)
  rw [← sec_map_comp, kernel.lift_ι, hx, GlobalTheory.EtC.CupSpec.map_res]

theorem ker_comp_zero {X Y Z : Shv R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ (U : Scheme.{0}) (y : Sec X U), Sec.map f y = 0 → Sec.map g y = 0) : kernel.ι f ≫ g = 0 := by
  apply Sheaf.hom_ext
  ext U y
  refine (h U.unop (Sec.map (kernel.ι f) y) ?_).trans rfl
  rw [← sec_map_comp, kernel.condition]; rfl

end CrystallineSemistableComparison.SheafSectionLemmas
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace KummerTwistLemmas

theorem twLift {Q : ℕ} [NeZero Q] (i : ℤ) (G : Shv (ZMod Q)) (e : ∀ (U : Scheme.{0}), Prim Q Γ(U, ⊤) → Sec G U)
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q) : ULift.{1} (ZMod Q)) • e U ζ) :
    ∃ f : tw Q i ⟶ G, ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = e U ζ := by
  let L : ∀ (U : Scheme.{0}), (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Sec G U :=
    fun U => Finsupp.linearCombination (ULift.{1} (ZMod Q)) (e U)
  have hL : ∀ (U : Scheme.{0}), twRel Q i Γ(U, ⊤) ≤ LinearMap.ker (L U) := by
    intro U
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
    rw [hr U ζ ξ a h, sub_self]
  let η : (Scheme.Γ ⋙ GlobalTheory.EtC.twF Q i) ⟶ G.obj :=
    { app := fun U => ModuleCat.ofHom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop))
      naturality := fun U V g => by
        refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
        change (twRel Q i Γ(V.unop, ⊤)).liftQ (L V.unop) (hL V.unop)
            (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g).hom) (Finsupp.single ζ c))) =
          (G.obj.map g).hom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop) (Submodule.Quotient.mk (Finsupp.single ζ c)))
        rw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single]
        simp only [L, Finsupp.linearCombination_single, map_smul]
        congr 1
        exact (he g.unop ζ).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ _).symm η,
    fun U ζ => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ G).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(U, ⊤))
  refine h2.trans ?_
  change (twRel Q i Γ(U, ⊤)).liftQ (L U) (hL U) (Submodule.Quotient.mk (Finsupp.single ζ 1)) = e U ζ
  rw [Submodule.liftQ_apply]
  simp [L]

end KummerTwistLemmas

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.Data.ZMod.Units\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem pow_self {Q : ℕ} {A : Type} [CommRing A] (ζ : Prim Q A) : ζ.1 ^ Q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one Q ℤ
  have := congrArg (Polynomial.aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
  exact this

def pw {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ζ.2.1, by
    obtain ⟨c, hc⟩ := CyclicComplexMaps.cyc_dvd Q q (NeZero.ne Q) h
    have := congrArg (Polynomial.aeval ζ.1) hc
    rw [Polynomial.aeval_comp, map_mul, ζ.2.2, zero_mul] at this
    simpa using this⟩

theorem pw_val {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : (pw h ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem pw_map {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    (pw h ζ).map f = pw h (ζ.map f) := Subtype.ext (map_pow f _ _)

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ GlobalTheory.EtC.twF q i)).naturality g.op)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤))
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ GlobalTheory.EtC.twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem redSheaf (hG : E.InGen) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) :
    ∃ π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i), IsRedSh h i π ∧
      ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map π (twGen i ζ) =
        (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)) := by
  obtain ⟨π, hπ⟩ := KummerTwistLemmas.twLift i ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))
    (fun U ζ => (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)))
    (fun g ζ => by
      change Sec.res g (twGen i (pw h ζ)) = twGen i (pw h (ζ.map g.appTop.hom))
      rw [twGen_res, pw_map])
    (fun U ζ ξ a ha => by
      let a' : (ZMod q)ˣ := ZMod.unitsMap h a
      have hξ : (pw h ξ).1 = (pw h ζ).1 ^ (a' : ZMod q).val := by
        rw [pw_val, pw_val, ha, ← pow_mul, mul_comm, pow_mul]
        have h1 : ((pw h ζ).1) ^ q = 1 := pow_self (pw h ζ)
        rw [← pw_val h ζ, pow_eq_pow_mod _ h1, pow_eq_pow_mod ((a' : ZMod q).val) h1]
        have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
          change (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
          rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
        rw [hv, Nat.mod_mod]
      have := ((hG q i).2.2 U (pw h ζ) (pw h ξ) a' hξ)
      change twGen i (pw h ξ) = (ULift.up (ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) : ULift.{1} (ZMod q)) • twGen i (pw h ζ)
      rw [this, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      congr 1
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
      simp only [a', ZMod.unitsMap]
      rw [← map_zpow]
      rfl)
  refine ⟨π, fun U ζ ξ hξ => ?_, hπ⟩
  rw [hπ U ζ, show pw h ζ = ξ from Subtype.ext (show (pw h ζ).1 = ξ.1 from hξ.symm)]

end CrystallineSemistableComparison.TwSeq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem sec_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (k • f) x = k • Sec.map f x := map_nsmul (CupSpec.mapHom X Y x) k f

theorem sec_map_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map f (k • x) = k • Sec.map f x := map_nsmul (f.hom.app (op U)).hom k x

theorem res_nsmul {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (k : ℕ) (x : Sec X U) :
    Sec.res g (k • x) = k • Sec.res g x := map_nsmul (X.obj.map g.op).hom k x

theorem res_zero {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec X U) = 0 :=
  map_zero (X.obj.map g.op).hom

theorem sec_map_zero' {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U : Scheme.{0}} : Sec.map f (0 : Sec X U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem sec_char {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (x : Sec F U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_self]
    rfl
  rw [this, zero_smul]

theorem morph_zero_of_sec {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y)
    (h : ∀ (U : Scheme.{0}) (x : Sec X U), Sec.map f x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem loc_of_img {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U V : Scheme.{0}} (g : V ⟶ U) (y : Sec Y U)
    (x : Sec X V) (hx : Sec.map f x = Sec.res g y) :
    Loc V fun W k => ∃ x' : Sec X W, Sec.map f x' = Sec.res (k ≫ g) y :=
  SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true V) fun W k _ => ⟨Sec.res k x, by rw [← CupSpec.map_res, hx, TwSec.res_comp]⟩

theorem twSeq (hG : E.InGen) : InTwSeq := by
  intro p a b _ i
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, hπ, hπg⟩ := redSheaf hG (dvdB p a b) i
  obtain ⟨π', hπ', hπ'g⟩ := redSheaf hG (dvdA p a b) i
  obtain ⟨m, hmdef⟩ : ∃ m : tw (p ^ (a + b)) i ⟶ tw (p ^ (a + b)) i, m = p ^ b • 𝟙 _ := ⟨_, rfl⟩
  have hm : ∀ (U : Scheme.{0}) (x : Sec (tw (p ^ (a + b)) i) U), Sec.map m x = p ^ b • x := fun U x => by
    rw [hmdef]; exact sec_nsmul _ _ x
  have hw : m ≫ π = 0 := morph_zero_of_sec _ fun U x => by
    change Sec.map π (Sec.map m x) = 0
    rw [hm, sec_map_nsmul]
    exact sec_char (q := p ^ b) (F := tw (p ^ b) i) (Sec.map π x)
  have hQ : p ^ a • m = 0 := by
    rw [hmdef, smul_smul, ← pow_add]
    exact morph_zero_of_sec _ fun U x => by rw [sec_nsmul]; exact sec_char x

  have hπepi : Epi π := by
    refine SheafSectionLemmas.epi_of_loc π fun U y => ?_
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hy : y = 0 := by
        have h0 := sec_char (q := p ^ b) (F := tw (p ^ b) i) y
        have h1 : p ^ b = 1 := by rw [hb, pow_zero]
        exact (one_nsmul y).symm.trans ((congrArg (fun n : ℕ => n • y) h1.symm).trans h0)
      exact SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true U) fun V g _ => ⟨0, by rw [sec_map_zero', hy]; exact (res_zero g).symm⟩
    · refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ b) i U y) fun V g hy => ?_
      rcases hy with hy | ⟨ξ, c, hy⟩
      · exact loc_of_img π g y 0 (by rw [sec_map_zero']; exact hy.symm)
      · refine SheafSectionLemmas.loc_mono (KummerTwistLemmas.rootLoc p a b hb V ξ) fun W k ⟨ζ, hζ⟩ => ⟨c • twGen i ζ, ?_⟩
        rw [sec_map_nsmul, hπg]
        change c • twGen i (pw (dvdB p a b) ζ) = Sec.res (k ≫ g) (show Sec (tw (p ^ b) i) U from y)
        rw [TwSec.res_comp, hy, res_nsmul, twGen_res]
        congr 2
        apply Subtype.ext
        change ζ.1 ^ (p ^ (a + b) / p ^ b) = (k.appTop.hom) ξ.1
        rw [← hζ, Nat.pow_div (Nat.le_add_left b a) (Nat.pos_of_ne_zero hp), Nat.add_sub_cancel]

  have hepi : Epi (kernel.lift π m hw) := by
    refine SheafSectionLemmas.epi_lift_of_loc m π hw fun U y hy => ?_
    refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · exact loc_of_img m g y 0 (by rw [sec_map_zero']; exact hy'.symm)
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact loc_of_img m g y 0 ((SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _)
      · have h0 : c • twGen i (pw (dvdB p a b) ζ) = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', sec_map_nsmul, hπg] at this
          exact this
        obtain ⟨d, rfl⟩ := (hG (p ^ b) i).2.1 V (pw (dvdB p a b) ζ) c h0
        exact loc_of_img m g y (d • twGen i ζ) (by rw [hm, smul_smul, hy'])

  have hker : kernel.ι m ≫ π' = 0 := by
    refine SheafSectionLemmas.ker_comp_zero m π' fun U y hy => ?_
    refine SheafSectionLemmas.sec_eq_of_loc _ _ (SheafSectionLemmas.loc_mono (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_)
    rw [res_zero, CupSpec.map_res]
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · rw [hy', sec_map_zero']
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact (SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _
      · have h0 : (p ^ b * c) • twGen i ζ = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', hm, smul_smul] at this
          exact this
        have hd := (hG (p ^ (a + b)) i).2.1 V ζ _ h0
        rw [pow_add, mul_comm (p ^ a)] at hd
        obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos (Nat.pos_of_ne_zero hp) b) hd
        rw [hy', sec_map_nsmul, hπ'g, ← smul_smul]
        exact sec_char (q := p ^ a) (F := tw (p ^ a) i) _

  obtain ⟨e, hedef⟩ : ∃ e, e = kernel.lift π m hw := ⟨_, rfl⟩
  have he : e ≫ kernel.ι π = m := by rw [hedef]; exact kernel.lift_ι _ _ _
  have : Epi e := by rw [hedef]; exact hepi
  have hz : kernel.ι e ≫ π' = 0 := by
    have h1 : kernel.ι e ≫ m = 0 := by rw [← he, kernel.condition_assoc, zero_comp]
    rw [← kernel.lift_ι m (kernel.ι e) h1, Category.assoc, hker, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l, e ≫ l = π' := ⟨Abelian.epiDesc e π' hz, Abelian.comp_epiDesc e π' hz⟩
  have hcomp : kernel.ι π ≫ π' = p ^ b • l := by
    apply (cancel_epi e).1
    have h2 : e ≫ kernel.ι π ≫ π' = m ≫ π' := by rw [← Category.assoc, he]
    rw [h2, Preadditive.comp_nsmul, hl, hmdef, Preadditive.nsmul_comp, Category.id_comp]
  have htor : p ^ a • kernel.ι π = 0 := by
    apply (cancel_epi e).1
    rw [Preadditive.comp_nsmul, he, hQ, comp_zero]
  exact ⟨π, π', l, hπ, hπ', hπepi, htor, hcomp⟩

end CrystallineSemistableComparison.TwSeq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace CrystallineSemistableComparison

theorem bock : BocksteinInputFromFormal := fun hF => bock_tw (TwSeq.twSeq hF.et.gen) hF

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace RootOfUnityLemmas

theorem pick_neg {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  rw [dite_eq_right h]

theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : x.cast hn hi = 0) : x = 0 := by
  subst hn; subst hi; exact h

theorem res_id {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (a : Sec F X) : Sec.res (𝟙 X) a = a := by
  simp [Sec.res]

theorem resGen_closed (hF : FormalIn) (q : ℕ) (s : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    Sec.map ((res _ (tw q s)).d 0 1) (resGen s ζ) = 0 := by
  obtain ⟨-, e, -, he⟩ := hF.a9 (ZMod q) (tw q s)
  obtain ⟨α, -, hα⟩ := he X (twGen s ζ)
  have h := ((hF.et.sch (ZMod q) X (res _ (tw q s)) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
  rw [hα] at h
  exact h

theorem ev_vanish {R : Type} [CommRing R] {X : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0) :
    ∀ (p : ℕ), p ≠ 0 → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U), ev α p s h U x = 0 := by
  intro p hp
  obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact fun s h' U x => h p' s h' U x

theorem isAW_conc {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}}
    (α : Cochain ((chains R).obj (sch.obj X)) I 0) (β : Cochain ((chains R).obj (sch.obj X)) J 0)
    (γ : Cochain ((chains R).obj (sch.obj X)) K (0 + 0)) (a : Sec (I.X 0) X) (b : Sec (J.X 0) X) (c : Sec (K.X 0) X)
    (hc : μ.mul X 0 0 0 (add_zero 0) a b = c)
    (hα0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 0 (by simp) U x = Sec.res x a)
    (hα1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0)
    (hβ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev β 0 0 (by simp) U x = Sec.res x b)
    (hβ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev β (p + 1) s h U x = 0)
    (hγ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 0 (0 + 0) (by simp) U x = Sec.res x c)
    (hγ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + (0 + 0) = s) (U : Scheme.{0}) (x : U ⟶ X), ev γ (p + 1) s h U x = 0) :
    μ.IsAW rfl α β γ := by
  intro N w h U x
  cases N with
  | zero =>
    subst h
    rw [Fin.sum_univ_one]
    have e1 : ev γ 0 (-((0 : ℕ) : ℤ) + (0 + 0)) rfl U x = μ.mul U 0 0 0 (add_zero 0) (ev α 0 0 (by simp) U x)
        (ev β 0 0 (by simp) U x) := by
      rw [hα0, hβ0, ← μ.nat, hc]
      exact hγ0 U x
    rw [e1]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rfl
  | succ N =>
    rw [hγ1 N w h U x]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hp : (p : ℕ) = 0
    · rw [ev_vanish β hβ1 (N + 1 - p) (by omega)]
      simp
    · rw [ev_vanish α hα1 p hp]
      simp

theorem conc_eq_one (hF : FormalIn) (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (t : ℤ) (ht : (0 : ℤ) = t)
    (c : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q t)) (0 + 0))
    (hc : ev c.1 0 (0 + 0) (by simp) X (𝟙 X) = resGen t ζ) (hn : (0 : ℤ) = 0 + 0) :
    CohomologyClass.mk c = (one q (sch.obj X)).cast hn ht := by
  subst ht
  by_cases hw : ∃ c' : Ht q (sch.obj X) 0 0, ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c' ∧
      ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ'
  · obtain ⟨α, hα, hα'⟩ : ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 0)) 0,
        CohomologyClass.mk α = one q (sch.obj X) ∧
        ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ' :=
      pick_spec hw
    rw [← hα]
    change CohomologyClass.mk c = CohomologyClass.mk α
    exact WeightedPowerFormIntegrability.mk_eq_of_ev hF.et.sch c α (hc.trans (hα' X (𝟙 X) ζ).symm)
  · have h1 : one q (sch.obj X) = 0 := pick_neg hw
    have hinv : Inv q (sch.obj X) := fun U ⟨x⟩ => (Prim.map (show U ⟶ X from x).appTop.hom ζ).2.1
    have h2 := (hF.a6ring q (sch.obj X)).1 hinv (CohomologyClass.mk c)
    rw [h1, map_zero, AddMonoidHom.zero_apply] at h2
    rw [h1, cast_zero', eq_zero_of_cast _ _ _ h2.symm]

end RootOfUnityLemmas


open RootOfUnityLemmas in
theorem root : RootsOfUnityFormal := by
  intro hF q _ X ⟨ζ⟩ i
  have hS := hF.et.sch
  obtain ⟨v, hv0, hv1⟩ := (hS (ZMod q) X (res _ (tw q (-i))) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen (-i) ζ) (resGen_closed hF q (-i) ζ)
  obtain ⟨u, hu0, hu1⟩ := (hS (ZMod q) X (res _ (tw q i)) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen i ζ) (resGen_closed hF q i ζ)
  obtain ⟨c, hc0, hc1⟩ := (hS (ZMod q) X (res _ (tw q (-i + i))) (-1) (0 + 0) 1 (by norm_num) (by norm_num)).1
    (resGen (-i + i) ζ) (resGen_closed hF q (-i + i) ζ)
  refine ⟨CohomologyClass.mk u, CohomologyClass.mk v, ?_⟩
  have hcup : cup q (CohomologyClass.mk v) (CohomologyClass.mk u) = CohomologyClass.mk c :=
    Pair.cup_spec (twPair q (-i) i) (sch.obj X) rfl v u c
      (isAW_conc (twPair q (-i) i) v.1 u.1 c.1 (resGen (-i) ζ) (resGen i ζ) (resGen (-i + i) ζ)
        (hF.et.tw q (-i) i X ζ) hv0 hv1 hu0 hu1 hc0 hc1)
  rw [hcup]
  exact conc_eq_one hF q X ζ (-i + i) (by ring) c ((hc0 X (𝟙 X)).trans (res_id _)) (by ring)

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

theorem zIn (h : FormalIn) (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : ZIn :=
  ⟨h.a6nat, h.a6ring, h.a9, h.et.a11, h4, h8, bock h, root h, sum h⟩

theorem etSide : EtaleSideSmoothAndSemistable := fun h l _ K _ =>
  ⟨adic h l K _ (fun _ hM => hM.1) (comp l K).1 fun M hM => _root_.CrystallineSemistableComparison.geoMain l K M hM.1,
    adic h l K _ (fun _ hM => hM) (comp l K).2 fun M hM => _root_.CrystallineSemistableComparison.geoMain l K M hM⟩

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

end CrystallineSemistableComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf =====
