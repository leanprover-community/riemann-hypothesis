module

public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  first | exact @GlobalTheory.HatNF.radial_mulG | exact GlobalTheory.HatNF.radial_mulG | (intros; apply GlobalTheory.HatNF.radial_mulG <;> assumption)
