module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaTorsionTranslates
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cosetIndicatorTheta_torsionTranslates : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), IsSdLat L → IsSdLat L' → 0 < c → Pres D (TaylorLogMetric.tor0 D cc dl) (s.lat L) (s.lat L') (B.thMoved a b (s.lat L) (s.lat L')) (toHost s fun z => ((ambOf s B χ cD).chiF a b L L')⁻¹ * (ambOf s B χ cD).thInd S L L' c x z) ((c : ℝ) ^ (Module.finrank ℚ X.E * a * b)) := by
  first | exact @GlobalTheory.ColNorms.IndPres.pres_thInd | exact GlobalTheory.ColNorms.IndPres.pres_thInd | (intros; apply GlobalTheory.ColNorms.IndPres.pres_thInd <;> assumption)
