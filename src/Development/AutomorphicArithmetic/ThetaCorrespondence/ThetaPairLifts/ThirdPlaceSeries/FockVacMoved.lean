module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepMove
section Lattices
open GlobalTheory.FinPl hiding Pl
variable {D : D7}
end Lattices
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
end Gen
theorem fock_vac_moved_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P))) ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j hj g g' hg hg' M M' hM hM' hm hm'
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sd : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((_root_.GlobalTheory.Fam.pk_z W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  exact gen (W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj) (sd j (by omega)) hM (sd (j + 1) hj) hM' hg hg' (hm _) (hm' _) _ _
    (W.Q.charW.base.chain.vY W.P.A3.A.μ0 j hj).1
end GlobalTheory.StepMove
end
end
