module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame, Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso

-- ===== clump member: Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def IsInP (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X.IsHermitian ∧ ∀ i j, ε i = ε j → X i j = 0

def realRank : ℕ := min (Fintype.card {i // ε i = true}) (Fintype.card {i // ε i = false})

end Matrices

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.FrameIsoReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem cT_star (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem signFrame_map (h : IsCMExt F E σ) (τ : EmbOver E w) {ε : Fin n → Bool}
    {b : GL (Fin n) (w.Completion ⊗[F] E)} (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) :
    (b.1.map (infEmb τ))ᴴ * J.map τ.1 * b.1.map (infEmb τ) = Formalism.REAL.Jm ε := by
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1).map (infEmb τ) =
      (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1).map (infEmb τ) :=
    congrArg (fun M => M.map (infEmb τ)) hb
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)] at h1
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  have h3 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1).map (infEmb τ) =
      (b.1.map (infEmb τ))ᴴ := by
    ext i j; exact (infEmb_sigR h τ _).symm
  rw [h2, h3] at h1
  rw [h1, Formalism.REAL.Jm]
  congr 1; funext i; split_ifs <;> simp

section Frame

variable (σ J) (h : IsCMExt F E σ) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E))

abbrev fB : Matrix (Fin n) (Fin n) ℂ := b.1.map (infEmb τ)

abbrev fBi : Matrix (Fin n) (Fin n) ℂ := (b⁻¹).1.map (infEmb τ)

theorem fBi_mul : fBi τ b * fB τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fB_mul : fB τ b * fBi τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_eq (g : GArch σ J w) :
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = fBi τ b * (archEquiv J h τ g).1.1 * fB τ b := by
  rw [archEquiv_val]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, Units.val_mul, Matrix.map_mul]

include h in
theorem isEmbedding_inFrame : Topology.IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b) := by
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b =
      (fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b) ∘ GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) := by
    funext g
    exact (inFrame_eq σ J h τ b g).trans rfl
  have hc : Topology.IsEmbedding fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b :=
    Function.LeftInverse.isEmbedding (f := fun x => fB τ b * x * fBi τ b) (fun x => by
      simp only [← mul_assoc, fB_mul, one_mul]; rw [mul_assoc, fB_mul, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  rw [e]
  exact hc.comp (GlobalTheory.Orb.isEmbedding_archMat J h τ)

variable {ε}

include h in
theorem inFrame_mem (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.inUJ ε (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  have hA : ((archEquiv J h τ g).1.1)ᴴ * J.map τ.1 * (archEquiv J h τ g).1.1 = J.map τ.1 := by
    rw [← cT_star]; exact (archEquiv J h τ g).2
  rw [Formalism.REAL.inUJ, inFrame_eq σ J h]
  set A := (archEquiv J h τ g).1.1
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  calc (Bi * A * B)ᴴ * Formalism.REAL.Jm ε * (Bi * A * B)
      = Bᴴ * Aᴴ * (Biᴴ * (Bᴴ * T * B) * Bi) * A * B := by
        rw [← hS]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * (Aᴴ * T * A) * B := by rw [hT]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hA, hS]

def hom0 : GArch σ J w →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((MulAut.conj b⁻¹).toMonoidHom.comp (matHom _ σ J))

theorem coe_archimedeanFrameConjMatrixHom (g : GArch σ J w) : ((hom0 σ J τ b g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := by
  simp [hom0, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame]

include h in
theorem exists_inFrame_eq (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (a : Formalism.REAL.UJ ε) :
    ∃ g : GArch σ J w, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  let bU : (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.map (infEmb τ).mapMatrix.toMonoidHom b
  have hbU : (bU : Matrix (Fin n) (Fin n) ℂ) = fB τ b := rfl
  have hbUi : ((bU⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = fBi τ b := by
    rw [← map_inv]; rfl
  let yU : (Matrix (Fin n) (Fin n) ℂ)ˣ := bU * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) * bU⁻¹
  set x := ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hx : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := a.2
  have hy : (yU : Matrix (Fin n) (Fin n) ℂ) = fB τ b * x * fBi τ b := by
    simp only [yU, Units.val_mul, hbU, hbUi, x]
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmem : yU ∈ Formalism.UG.UJ (starRingEnd ℂ) T := by
    change Formalism.UG.cT (starRingEnd ℂ) (yU : Matrix (Fin n) (Fin n) ℂ) * T * (yU : Matrix (Fin n) (Fin n) ℂ) = T
    rw [cT_star, hy]
    calc (B * x * Bi)ᴴ * T * (B * x * Bi) = Biᴴ * (xᴴ * (Bᴴ * T * B) * x) * Bi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hS, hx, ← hS, hT]
  refine ⟨(archEquiv J h τ).symm ⟨yU, hmem⟩, ?_⟩
  rw [inFrame_eq σ J h, MulEquiv.apply_symm_apply]
  change Bi * (yU : Matrix (Fin n) (Fin n) ℂ) * B = x
  rw [hy]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc, fBi_mul, Matrix.mul_one, Matrix.one_mul]

def frameHom (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w →* Formalism.REAL.UJ ε :=
  (hom0 σ J τ b).codRestrict _ fun g => by
    change Formalism.REAL.inUJ ε _
    rw [coe_archimedeanFrameConjMatrixHom]; exact inFrame_mem σ J h τ b hb g

theorem frameHom_val (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.coeMatrixAlt ε (frameHom σ J h τ b hb g) = GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := coe_archimedeanFrameConjMatrixHom σ J τ b g

theorem frameHom_bijective (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : Function.Bijective (frameHom σ J h τ b hb) := by
  refine ⟨fun g g' e => (isEmbedding_inFrame σ J h τ b).injective ?_, fun a => ?_⟩
  · rw [← frameHom_val σ J h τ b hb, ← frameHom_val σ J h τ b hb, e]
  · obtain ⟨g, hg⟩ := exists_inFrame_eq σ J h τ b hb a
    exact ⟨g, Formalism.REAL.injective_coeMatrix ε ((frameHom_val σ J h τ b hb g).trans hg)⟩

def frameEquiv (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w ≃ₜ* Formalism.REAL.UJ ε :=
  { MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb) with
    continuous_toFun := ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding).continuous_iff.2
      ((isEmbedding_inFrame σ J h τ b).continuous.congr fun g => (frameHom_val σ J h τ b hb g).symm)
    continuous_invFun := (isEmbedding_inFrame σ J h τ b).continuous_iff.2 ((Formalism.REAL.continuous_coeMatrix ε).congr fun x => by
      have := frameHom_val σ J h τ b hb ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).symm x)
      exact (congrArg (Formalism.REAL.coeMatrixAlt ε)
        ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).apply_symm_apply x).symm).trans this) }

end Frame

end GlobalTheory.FrameIsoReal
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso =====
