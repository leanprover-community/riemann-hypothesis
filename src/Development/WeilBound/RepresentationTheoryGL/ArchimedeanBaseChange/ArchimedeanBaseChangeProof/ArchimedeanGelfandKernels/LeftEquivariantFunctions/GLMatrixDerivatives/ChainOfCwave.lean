module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCwaveB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.RCalc (isOpen_GLs differentiableAt_of_smooth)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem good_smul_bump_of_isWave {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u)
    (g : ℝ → ℝ) (T : ℝ) (hg : IsBump g T) :
    Good (GLs n) (fun q : ℝ × Mat n => ((g q.1 : ℂ)) • u q.1 q.2) T := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((g q.1 : ℂ))) :=
      Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
    exact h1.contDiffOn.smul hu.1
  · intro t x ht
    simp [hg.2.2 t ht]

theorem paramInt : ParamInt := by
  intro n E u hu g T hg
  have hG := good_smul_bump_of_isWave E u hu g T hg
  refine ⟨good_smooth isOpen_GLs _ T hG, ?_⟩
  intro X x hx
  unfold Rd
  refine (good_fderiv_apply isOpen_GLs hG hx (x * X)).trans ?_
  congr 1
  funext t
  have hd : DifferentiableAt ℝ (u t) x := by
    apply differentiableAt_of_smooth _ hx
    have h2 : ContDiffOn ℝ ∞ (fun y : Mat n => Function.uncurry u (t, y)) (GLs n) :=
      hu.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _, hy⟩)
    exact h2
  have hf : fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x = ((g t : ℂ)) • fderiv ℝ (u t) x :=
    (hd.hasFDerivAt.const_smul ((g t : ℂ))).fderiv
  show (fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x) (x * X) = _
  rw [hf]
  rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
