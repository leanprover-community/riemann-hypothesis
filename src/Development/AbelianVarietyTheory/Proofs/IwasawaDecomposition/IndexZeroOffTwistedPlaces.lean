module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingOneApplyDivThree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr



theorem GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  intro K B f T w hO hF hP P x hη hW v hv j hj1 hj2
  classical
  let Zr : ReadL x.m.z.R x.m.z.F x.s.p0 x.r.Y := (x.rowsAre hη).Z
  obtain ⟨G, Y, -⟩ := GlobalTheory.PointGeometry.exists_geo (w.st x.o.Z).toD7.what₂.LL
  let Fm : ∀ k, GlobalTheory.ProvisionalDivX.MjForm (w.st x.o.Z).toD7 k := fun k =>
    ⟨mjH Zr k, jM Zr k, mjH_good Zr x.m.intersectionNumber_baseChange k, jM_basis Zr x.m.intersectionNumber_baseChange k, jM_lat Zr x.m.z.pins x.m.intersectionNumber_baseChange k,
      mjLat_sub Zr x.m.z.pins x.m.intersectionNumber_baseChange k, MjModel.jM_metric_all Zr x.m.intersectionNumber_baseChange k⟩
  let Xd : DivX (w.st x.o.Z).toD7 := GlobalTheory.provisionalDivX (w.st x.o.Z).toD7 G Y
    (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) Fm
  have hMj := mjHTie_of_eq Zr Xd rfl (HEq.refl (jM Zr))
  have hIdx : IdxDefs (w.st x.o.Z).toD7 Xd := (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Xd
  have hT := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y Zr Xd _ x.m.z.pins x.m.intersectionNumber_baseChange hMj hIdx
  have hv' : v ∉ x.m.z.W1 (F0K K.s (w.D x.o.Z)) := hW ▸ hv
  have h0 : x.r.Y.tup (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 = (w.D x.o.Z).what₂.mu0 := by
    rw [x.r.tup]; exact x.m.y.tup0
  have hIj := hT.Ij
  have hjw := hT.jw
  have hv2 := fun (i : Fin (w.st x.o.Z).toD7.R.m) (w' : HeightOneSpectrum (𝓞 (w.st x.o.Z).toD7.what₂.LL))
      (hw' : w' ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _)) =>
    not_or.1 (fun h => hv' ⟨i, w', hw', h⟩)
  have hm : (w.st x.o.Z).toD7.R.m = B.R.m := rfl
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st x.o.Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [← h0]
  have hp : (w.st x.o.Z).toD7.plEq v ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _) :=
    Set.mem_insert _ _
  refine ⟨?_, ?_⟩
  · exact (hIj i _ v).trans (not_not.1 (hv2 i _ hp).1)
  · exact (hjw i _ v).trans (not_not.1 (not_or.1 (hv2 i _ hp).2).1)
