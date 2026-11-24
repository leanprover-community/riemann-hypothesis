module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceComponentHeckeCharResidue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) → ∀ (χ : HChar D.host.E) (c : (kP s.w)ˣ →* ℂˣ), IsRes χ s.w c → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = c w := by
  first | exact @GlobalTheory.XiRes.exists_isCompAt_res | exact GlobalTheory.XiRes.exists_isCompAt_res | (intros; apply GlobalTheory.XiRes.exists_isCompAt_res <;> assumption)
