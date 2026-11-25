module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.PicardGroup

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta Formalism.MainNotions.StandardLattice GlobalTheory.Mem.Th Filter Topology
open Formalism.IndefR.Lev (finE swapAE EAf)
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)

def frL (u : ι → GL (Fin n) ℂ) (y : Frames G) : Frames G :=
  ⟨fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ) * y.1 τ, fun τ => by
    rw [det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (u τ).isUnit).mul (y.2 τ)⟩

def lT (u : ι → GL (Fin n) ℂ) : (Frames G → ℂ) →ₗ[ℂ] (Frames G → ℂ) := LinearMap.funLeft ℂ ℂ (frL G u)

omit [Fintype ι] in
theorem lT_apply (u : ι → GL (Fin n) ℂ) (F : Frames G → ℂ) (y : Frames G) : lT G u F y = F (frL G u y) := rfl

omit [Fintype ι] in
theorem lT_mul (u v : ι → GL (Fin n) ℂ) (F : Frames G → ℂ) : lT G (u * v) F = lT G v (lT G u F) :=
  funext fun y => congrArg F (Subtype.ext (funext fun τ => Matrix.mul_assoc _ _ _))

omit [Fintype ι] in
theorem lT_one (F : Frames G → ℂ) : lT G 1 F = F :=
  funext fun y => congrArg F (Subtype.ext (funext fun τ => Matrix.one_mul _))

theorem lT_mem (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) {F : Frames G → ℂ} (hF : F ∈ ValC G lam) :
    lT G u F ∈ ValC G lam := by
  obtain ⟨P, hP, rfl⟩ := hF
  have h1 : CSpan lam ≤ VV ℂ lam := by
    refine (CSpan_le_span (RingHom.id ℂ) lam).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    simpa [MvPolynomial.map_id] using hF'
  have h2 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ)) P ∈ VV ℂ lam :=
    (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n _).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ))
      (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)
  have h3 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (u τ : Matrix (Fin n) (Fin n) ℂ)) P ∈ CSpan lam := by
    simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ h2
  refine ⟨(∏ τ, (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ shiftOf lam τ) • _, Submodule.smul_mem _ _ h3, ?_⟩
  funext y
  rw [map_smul, Pi.smul_apply, smul_eq_mul, lT_apply]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, det_mul, mul_zpow, Finset.prod_mul_distrib,
    mul_assoc, Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly]
  congr 3
  simp [Matrix.mul_apply]

end Tr

section Val

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

def valL (b : S.β) (d : S.D b) : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] (Fr emb σ n → ℂ) :=
  (S.trTo emb σ b d).toLinearMap ∘ₗ LinearMap.proj (S.cl b d)

variable {S emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}

variable (S emb σ lam) in
def prFi : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] S.Fi emb σ lam :=
  (LinearMap.exists_leftInverse_of_injective (S.Fi emb σ lam).subtype (Submodule.ker_subtype _)).choose

end Val

section Comp

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {ι : Type} (t : ι ≃ D.what₂.Tau)

def finN : GA D V →* GL (Fin n) (AfE D.host.F D.host.E) := by
  subst hn
  exact finE V

def infN : GA D V →* (ι → GL (Fin n) ℂ) := by
  subst hn
  exact MonoidHom.pi fun τ => (Formalism.UG.bc (θ (t τ))).comp (infHom V)

theorem finN_apply (g : GA D V) (i j : Fin n) : (finN V hn g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) i j =
    (finE V g).1 (Fin.cast hn.symm i) (Fin.cast hn.symm j) := by
  subst hn
  rfl

variable {V}

theorem finN_of_inf {k : GA D V} (hk : k ∈ GinfC V) : finN V hn k = 1 := by
  subst hn
  show Formalism.UG.bc (swapAE D) (finHom V k) = 1
  rw [show finHom V k = 1 from hk, map_one]

theorem infN_of_fin {k : GA D V} (hk : k ∈ GfC V) : infN θ V hn t k = 1 := by
  subst hn
  funext τ
  show Formalism.UG.bc (θ (t τ)) (infHom V k) = 1
  rw [show infHom V k = 1 from hk, map_one]

theorem swapAE_sig (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig z) = Formalism.UG.sigR D.sp.cm.sig _ (swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem JR_one (hG : V.gram = 1) (A : Type) [CommRing A] [Algebra D.host.F A] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := D.host.F) A V.gram = 1 := by
  rw [hG, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finN_mem (hG : V.gram = 1) (g : GA D V) : finN V hn g ∈ UAd D.sp.cm n := by
  subst hn
  have h : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) (finHom V g).1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram * (finHom V g).1 =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR _ V.gram := GlobalTheory.UnitarySplit.finHom_mem V g
  rw [JR_one hG, mul_one] at h
  have h2 := congrArg (fun M => Matrix.map M (swapAE D)) h
  simp only [Matrix.map_mul] at h2
  rw [PtExist.mem_uad_iff, ← Matrix.map_one (swapAE D) (map_zero _) (map_one _), ← h2]
  congr 1
  exact Matrix.ext fun i j => (swapAE_sig _).symm

theorem isAniso_of_gram (hG : V.gram = 1) : IsAniso V := by
  rintro r C ⟨hr, hC, h0⟩
  have h1 := congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩
  rw [hG, Matrix.mul_one, Matrix.mul_apply] at h1
  have h2 := congrArg D.host.φ₀ h1
  have h3 : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) := D.sp.cm.cmUnram.2.1 _
  have h4 : ∑ i, Complex.normSq (D.host.φ₀ (C i ⟨0, hr⟩)) = 0 := by
    apply Complex.ofReal_injective

    rw [map_sum] at h2
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← map_zero D.host.φ₀]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
    rw [map_mul, Complex.normSq_eq_conj_mul_self, ← h3]
    rfl
  refine hC.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 h4 i (Finset.mem_univ i)
  simpa using this

end Comp

end GlobalTheory.Mem.ColAd

end
