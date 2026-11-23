module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


section Gen
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))
theorem hkDat_of_hkDat_datL (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {i k Q α Rr} (h : HkDat (datL x L).R (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(h.split), (h.offS), (h.odd), (h.le), (h.elt), (h.reps)⟩
theorem eigVec_eW_of_hkDat_good_index (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (eigAd_iff_eigVec x.r.Y l.rat.In.Sb l.rat.In.eig).mp l.rat.rat.eig i σ k Q α Rr hd hσ y hy)
theorem eigAd_smallPlaceSet_of_yRel (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (smallPlaceSet L l) (localEigenvalueDegree L l) := by
  apply (eigAd_iff_eigVec Y (smallPlaceSet L l) (localEigenvalueDegree L l)).2
  intro i σ k Q α Rr hd hσ y hy
  with_unfolding_all
    exact EigVec.congr (v' := Y.mj.eW i y)
      (eigVec_loc L (eigVec_eW_of_hkDat_good_index l i σ k Q α Rr
        (hkDat_of_hkDat_datL L l hd) hσ y hy)) (hY.eW i y)
end GlobalTheory.HeightCounting.Fin3
end
end
