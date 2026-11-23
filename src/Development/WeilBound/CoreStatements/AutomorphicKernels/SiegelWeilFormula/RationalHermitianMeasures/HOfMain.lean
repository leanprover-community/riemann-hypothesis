module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.IncMScalarMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Rat

variable {d : SD σ} {η : E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}

theorem mem_ratHerm {S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n} :
    S ∈ MeasP.ratHerm F E σ d.n ↔ ∃ M : Matrix (Fin d.n) (Fin d.n) E, incM F M = (S.1 : Mx F E d.n d.n) := by
  simp only [MeasP.ratHerm, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  rfl

def ratE (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    MeasP.ratHerm F E σ d.n ≃ nF σ d.Y d.b where
  toFun S := ⟨(hEq hOf hne hof herm).symm S.1, by
    rw [mem_nF_iff]
    obtain ⟨M, hM⟩ := mem_ratHerm.1 S.2
    refine ⟨-(η • Mᵀ), ?_⟩
    show -(inclR (F := F) (AF F) η • ((S.1).1 : Mx F E d.n d.n)ᵀ) = _
    rw [← hM]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  invFun γ := ⟨hEq hOf hne hof herm γ.1, by
    rw [mem_ratHerm]
    obtain ⟨T, hT⟩ := (mem_nF_iff γ.1).1 γ.2
    refine ⟨-(η⁻¹ • Tᵀ), ?_⟩
    show _ = ((hOf γ.1).1 : Mx F E d.n d.n)
    rw [hOf_val hOf hne hof, hT]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  left_inv S := Subtype.ext ((hEq hOf hne hof herm).apply_symm_apply S.1)
  right_inv γ := Subtype.ext ((hEq hOf hne hof herm).symm_apply_apply γ.1)

end Rat

theorem meas_hOf {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : Rel d R x t u T η T₀ hOf θ fr g)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    MeasurableEmbedding hOf ∧ (lam.map hOf).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (MeasP.ratHerm F E σ d.n) (hOf '' 𝓖) (lam.map hOf) ∧ lam.map hOf (hOf '' 𝓖) = 1 := by
  have hσ := sigma_sigma_of_good d.ok.good
  obtain ⟨-, -, -, hbo⟩ := nA_top hσ d.ok.frame
  haveI := hbo
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) := ⟨rfl⟩
  obtain ⟨-, hlam, hfd, h1⟩ := hc
  haveI := hlam
  let e := hEq hOf hR.ne hR.hof hR.herm
  let eM := e.toHomeomorph.toMeasurableEquiv
  have hemb : MeasurableEmbedding hOf := eM.measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact e.toAddEquiv.isAddHaarMeasure_map lam e.continuous e.symm.continuous
  · refine hfd.image_of_equiv eM.toEquiv (eM.measurePreserving_symm lam).quasiMeasurePreserving
      (ratE hR.ne hR.hof hR.herm) ?_
    intro S β
    show e (e.symm S.1 + β) = S.1 + e β
    rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]

end PositivityTheory.SiegelWeilFormula.MeasD

end
