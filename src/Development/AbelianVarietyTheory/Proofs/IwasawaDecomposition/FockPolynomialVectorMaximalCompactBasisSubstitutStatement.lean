module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_basis_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  first | exact @GlobalTheory.FockSubst.pureTensorO_subst | exact GlobalTheory.FockSubst.pureTensorO_subst | (intros; apply GlobalTheory.FockSubst.pureTensorO_subst <;> assumption)
