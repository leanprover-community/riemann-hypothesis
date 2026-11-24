module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]

def IsIso {n : ℕ} (P : CG E n) {ι : Type} [Fintype ι] {m : ι → ℕ} (Ps : ∀ i, CG E (m i)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (C : Multiset ℂˣ) (B : ι → Multiset ℂˣ),
    P.HasSat w C ∧ (∀ i, (Ps i).HasSat w (B i)) ∧ ∑ i, B i = C


end PositivityTheory.Rg.Tf.ChR
