module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
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

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.memberDictionary_frames_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  first | exact @GlobalTheory.Member.fr_orthonormal_unit | exact GlobalTheory.Member.fr_orthonormal_unit | (intros; apply GlobalTheory.Member.fr_orthonormal_unit <;> assumption)
