module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem isOfFinOrder_of_conjIn_mem_St :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  intro F E _ _ _ _ _ _ hc n J L β hU hβ u x hu
  open Matrix in
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    classical
    by_contra hspan
    have hproper : Submodule.span E (L : Set (Fin n → E)) < ⊤ := lt_top_iff_ne_top.mpr hspan
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
    let σ : E →+* E := hc.sig
    let z : Fin n → E := J⁻¹ *ᵥ (fun i => σ (f (Pi.single i 1)))
    have hpair (x : Fin n → E) : Formalism.UG.hform σ J x z = σ (f x) := by
      rw [Formalism.UG.P.hform_eq_dot, show J *ᵥ z = (fun i => σ (f (Pi.single i 1))) by
        simp only [z, mulVec_mulVec, J.mul_nonsing_inv hU.unit, one_mulVec], dotProduct]
      have hx : ∑ i, x i • Pi.single i (1 : E) = x := by
        simpa only [← Pi.single_smul', smul_eq_mul, mul_one] using
          LinearMap.sum_single_apply (fun _ : Fin n => E) x
      conv_rhs => rw [← hx, map_sum, map_sum]
      simp only [Function.comp_apply, LinearMap.map_smul, smul_eq_mul, map_mul]
    have hz : z ≠ 0 := by
      intro hz
      apply hf
      apply LinearMap.ext
      intro x
      apply σ.injective
      rw [LinearMap.zero_apply, map_zero, ← hpair, hz, Formalism.UG.P.csScale_hform_zero_right]
    have hann (x : Fin n → E) (hx : x ∈ L) : Formalism.UG.hform σ J x z = 0 := by
      have hfx : f x ∈ (Submodule.span E (L : Set (Fin n → E))).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span hx)
      rw [hmap, Submodule.mem_bot] at hfx
      rw [hpair, hfx, map_zero]
    have hzL : z ∈ L := by
      change z ∈ (L : Set (Fin n → E))
      rw [← hU.selfdual]
      intro x hx
      rw [hann x hx]
      exact (algebraMap (𝓞 E) E).range.zero_mem
    let v : InfinitePlace F := Classical.choice inferInstance
    let ι := v.embedding_of_isReal (hc.totReal.isReal v)
    rcases hU.tdef.2 ι with hpos | hneg
    · obtain ⟨a, ha, hsign⟩ := hpos z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
    · obtain ⟨a, ha, hsign⟩ := hneg z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hspan x
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  let H : Subgroup (UR hc J) :=
    (Formalism.UG.levelAfL hc.sig J L).comap (conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
  have hH : Finite H := by
    let f : H → Formalism.UG.stabAt (UQ hc J) ((Formalism.UG.levelAfL hc.sig J L).subgroupOf (UA hc J)) x :=
      fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt x γ.1).2 γ.2⟩
    refine Finite.of_injective f ?_
    intro a b hab
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))
  have huH : u ∈ H := by
    show conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ Formalism.UG.levelAfL hc.sig J L
    rw [← hb]
    refine ⟨?_, hu⟩
    rw [conjIn_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) (ratEl u).1.2) x.2
  have := isOfFinOrder_of_finite (⟨u, huH⟩ : H)
  exact H.subtype.isOfFinOrder this

end GlobalTheory.DefFree
