module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPow
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

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.CoprimeDescent.descent | exact GlobalTheory.KZ.ES.CoprimeDescent.descent | (intros; apply GlobalTheory.KZ.ES.CoprimeDescent.descent <;> assumption)
