module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedRadialOpsClosureAndFunctions
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

theorem _root_.GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → (PtB P Bs 1 ∧ (∀ a b, PtB P Bs a → PtB P Bs b → PtB P Bs (a * b))) ∧ PtB P Bs d.L.ζi ∧ PtB P Bs d.L.ζbi ∧ PtB P Bs (d.L.D * d.L.Dbi) ∧ PtB P Bs (d.L.Db * d.L.Di) ∧ PtB P Bs (d.L.Drb * d.L.Dri) ∧ PtB P Bs (d.L.Dr * d.L.Drbi) ∧ ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < dR P Bs x.1 x.2 ∧ 0 < gR P Bs x.1 x.2 ∧ nv (d.L.Di.1 Φ) x = (dR P Bs x.1 x.2)⁻¹ * nv Φ x ∧ nv ((TL.gI d.L).1 Φ) x = (gR P Bs x.1 x.2)⁻¹ * nv Φ x := by
  first | exact @GlobalTheory.HatNF.ptB_basic | exact GlobalTheory.HatNF.ptB_basic | (intros; apply GlobalTheory.HatNF.ptB_basic <;> assumption)
