module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BasePointLift

theorem exists_lift_of_ptOf : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) (k : TC.GA B (B.R.N i)), (∃ p : Formalism.L2.Col.DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) → ∃ kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i), kA ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) kA = k.1 := by
  intro B X I hI hP l Z i hi k hk
  obtain ⟨p, hp, -⟩ := hk
  have hu := hp.uni
  obtain ⟨-, -, -, hg⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hg1 := (hg i hi).1
  unfold Formalism.L2.Forms.gramN at hg1
  have hy : k ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
      (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).gram.reindex (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)) (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)))
      (FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    rw [hg1]
    change k ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)
    exact hu
  obtain ⟨a, ha, e⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM _ (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi) ⟨k, hy⟩
  exact ⟨a, ha, e⟩

end GlobalTheory.BasePointLift

end
