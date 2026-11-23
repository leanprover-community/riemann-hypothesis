module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitaryNormalVectorCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMapFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsomHTSymm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmpCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp



namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frame_fvec (t : TauC Y u u') (b : Fin (D.R.rS + 1)) : t.frame.fl.fvec b = t.lin ((X.Fu u').fvec b) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (mapLF t.lin (lf D (X.Fu u'))).fl.fvec b = _
  rw [mapLF_fl hγ, fvec_mapFlag]

theorem frame_z_eq_lin_zu (t : TauC Y u u') : t.frame.fl.z = t.lin (X.Fu u').z := by
  have := frame_fvec Y t (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem mem_frameX (t : TauC Y u u') (x : (VS D).V) : x ∈ t.frame.fl.X ↔ t.lin.symm x ∈ (X.Fu u').X :=
  CorankRelation.mem_Xsp_mapLF t.lin t.rep.2.2.1 (lf D (X.Fu u')) x

theorem omp_terms (t1 t2 : TauC Y u u') (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u'))) (he : t2.lin = σ * t1.lin * s') :
    omp (X.Fu u) t2.frame.fl = σ (omp (X.Fu u) t1.frame.fl) ∧
    Dl (X.Fu u) t2.frame.fl (D.R.rS + 1) = Dl (X.Fu u) t1.frame.fl (D.R.rS + 1) ∧
    omp t2.frame.fl (X.Fu u) = σ (omp t1.frame.fl (X.Fu u)) ∧
    Dl t2.frame.fl (X.Fu u) (D.R.rS + 1) = Dl t1.frame.fl (X.Fu u) (D.R.rS + 1) := by
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  obtain ⟨hσi, -, -⟩ := hσ
  obtain ⟨hσi', hσf', hσz'⟩ := hσ'
  obtain ⟨-, hsf, hsz⟩ := hs'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hγ2 : σ * t1.lin * s' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := he ▸ t2.rep.2.2.1
  obtain ⟨o1, o2, o3, o4⟩ := omp_coset (X.Fu u) (X.Fu u') σ t1.lin s' hσi hσi' hγ1 hγ2 hσf' hσz' hsf hsz
  have hF1 : t1.frame.fl = mapFlag t1.lin hγ1 (X.Fu u') := mapLF_fl hγ1 (lf D (X.Fu u'))
  have hF2 : ∀ b, t2.frame.fl.fvec b = (mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')).fvec b := fun b => by
    rw [frame_fvec, fvec_mapFlag, he]
  have hrefl : ∀ b, (X.Fu u).fvec b = (X.Fu u).fvec b := fun b => rfl
  obtain ⟨k1, k2⟩ := omp_congr (F := X.Fu u) (G := X.Fu u) hrefl hF2
  obtain ⟨k3, k4⟩ := omp_congr (F := t2.frame.fl) (G := mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')) hF2 hrefl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact k1.trans (o1.trans (congrArg (fun G => σ (omp (X.Fu u) G)) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k2).trans (o2.trans (congrArg (fun G => (Zhat (X.Fu u) G).det) hF1.symm))
  · exact k3.trans (o3.trans (congrArg (fun G => σ (omp G (X.Fu u))) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k4).trans (o4.trans (congrArg (fun G => (Zhat G (X.Fu u)).det) hF1.symm))

end Formalism.L2.SG.NGCut.NormalVectorPairings
