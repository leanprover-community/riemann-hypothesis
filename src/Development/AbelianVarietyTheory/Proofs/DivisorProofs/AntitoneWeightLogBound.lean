module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBound
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open scoped GlobalTheory.CompHt
namespace GlobalTheory.BergRank

open ReciprocityTheory.ChartRestriction.G.FD

theorem abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact abs_wtOf_le la _

theorem sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp; linarith
    · have hb := fun i => abs_le.1 (abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring

end GlobalTheory.BergRank
