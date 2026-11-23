module

public import Formalism.HermitianLattices.StatementLat
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.lattice_index_nonzero_iff_under_field_map : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  first | exact @GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | exact GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | (intros; apply GlobalTheory.LidxBaseChange.lidx_ne_zero_iff <;> assumption)
