module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisors
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (cj j h₀ x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x)) := by
  first | exact @GlobalTheory.DivTransfer.divAt_cj_iff | exact GlobalTheory.DivTransfer.divAt_cj_iff | (intros; apply GlobalTheory.DivTransfer.divAt_cj_iff <;> assumption)
