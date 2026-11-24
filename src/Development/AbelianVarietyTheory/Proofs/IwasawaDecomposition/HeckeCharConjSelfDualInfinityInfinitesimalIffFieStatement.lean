module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFie
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

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdInf_iff | exact GlobalTheory.CuspRep.csdInf_iff | (intros; apply GlobalTheory.CuspRep.csdInf_iff <;> assumption)
