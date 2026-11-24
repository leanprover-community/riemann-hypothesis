module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SJ.RowB

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iC_cpt_eq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, cpt, RingHom.id_apply]

theorem theta_eq : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y))) := by
  intro D Bs A X fc s R cr M eV hF hI y
  rw [M.cF_eq, hI y, M.eR_eq, X.rowMat_base cr true hF.h2, Matrix.one_mulVec, iC_cpt_eq, hF.theta y]
  rfl

end GlobalTheory.Mem.SJ.RowB

end
