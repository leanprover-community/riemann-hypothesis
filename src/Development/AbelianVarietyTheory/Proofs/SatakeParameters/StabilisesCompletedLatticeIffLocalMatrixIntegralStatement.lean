module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)), IsFrameAt V v h → ∀ g, (∀ w, w ≠ v → locMat hc V w g = 1) → (Stab hc V g ↔ h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range) := by
  first | exact @GlobalTheory.PlaceComp.StabLoc.stab_iff | exact GlobalTheory.PlaceComp.StabLoc.stab_iff | (intros; apply GlobalTheory.PlaceComp.StabLoc.stab_iff <;> assumption)
