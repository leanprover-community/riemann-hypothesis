module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

def dl (r : ℕ) (b : Fin (r + 1)) : F := if b = Fin.last r then 1 else 0

theorem e_ueq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    g.e ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) =
      (p1 g η * dl r b, p2 g η * dl r b + (g.q : F) * p2 g (l b)) := by
  have he : g.e (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = ((dl r b : F), (dl r b : F)) := by
    by_cases hb : b = Fin.last r
    · subst hb
      rw [show (((eV r : Fin (r + 1) → M.R) (Fin.last r) : M.R) : E) = 1 by simp [eV], map_one]
      simp only [dl, if_true]
      rfl
    · rw [show (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = 0 by simp [eV, hb], map_zero]
      simp only [dl, if_neg hb]
      rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, AddMemClass.coe_add, MulMemClass.coe_mul, map_add (f := _),
    map_mul, he, embedding_uniformizer]
  ext
  · simp [p1]
  · simp [p2]

theorem conj_map_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p1 g) = Zh.map (p2 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem conj_map_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p2 g) = Zh.map (p1 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem sum_dl (x : Fin (r + 1) → F) : ∑ b, x b * dl r b = x (Fin.last r) := by
  simp [dl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end Formalism.L2.SG.LocalCountModules.AlgGSplit
