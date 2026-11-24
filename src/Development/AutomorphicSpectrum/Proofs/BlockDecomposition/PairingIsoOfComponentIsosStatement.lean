module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.pairing_iso_of_component_isos : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | exact GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff <;> assumption)
