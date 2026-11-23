module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLift
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.baseSections_values_integral_at_coverLift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  first | exact @GlobalTheory.CoverLiftVal.le_one_at_lift | exact GlobalTheory.CoverLiftVal.le_one_at_lift | (intros; apply GlobalTheory.CoverLiftVal.le_one_at_lift <;> assumption)
