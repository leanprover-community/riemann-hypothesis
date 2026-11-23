module

public import Formalism.LocalToGlobal.HermitianColumns.TiedQC
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def redJ (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal)
    (x : GL (Fin (D.sp.X (D.R.m - 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) :
    Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v) :=
  redM D.host.F v ((F u).gl.mat a v hv (((F u).glev (D.R.m - 1) (Nat.sub_le _ _)).fr a v hv)
    (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ x))



structure TwistedJointForms (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) where

  J_g : ∀ u μ (h : 1 ≤ D.R.m - 1) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal),
    ∀ x ∈ levelVL D.sp.cm.sig (D.sp.X (D.R.m - 1)).gram v (T.levJ u μ h).Lb,
      x ∈ (T.levJ u μ h).Uloc v ↔ InJ (aOf D.R (D.R.m - 1)) D.R.t (D.R.N (D.R.m - 1)) false (redJ F u a v hv x)

  J_off : ∀ u μ (h : 1 ≤ D.R.m - 1) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ → v ∉ badG D →
    ((T.levJ u μ h).Uloc v).map (reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom =
      ((F u).cls (D.R.m - 1) (Nat.sub_le _ _)).lev.Uloc v

  yG : ∀ u μ (h : 1 ≤ D.R.m - 1), T.Yb u μ h → ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)),
    (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal → Fin (D.R.N (D.R.m - 1)) → kv D.host.F v
  yG_smul : ∀ u μ h (κ : (T.levJ u μ h).U) y a v hv,
    yG u μ h (κ • y) a v hv = redJ F u a v hv (bc (prV (E := D.host.E) v) κ.1) *ᵥ yG u μ h y a v hv

  yG_rep : ∀ u μ h β a v hv, yG u μ h (T.yb u μ h β) a v hv =
    fun b : Fin (D.R.N (D.R.m - 1)) => if (b : ℕ) = fcOf D.R (D.R.m - 1) then (1 : kv D.host.F v) else 0

  YQ : D.what₂.Word → D.what₂.Tup → 1 ≤ D.R.m - 1 → Type
  yQ : ∀ u μ h, T.Yb u μ h → YQ u μ h
  y_inj : ∀ u μ h y y', yG u μ h y = yG u μ h y' → yQ u μ h y = yQ u μ h y' → y = y'
  yQ_off : ∀ u μ h (κ : (T.levJ u μ h).U) y, (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → yQ u μ h (κ • y) = yQ u μ h y

end Formalism.L2.Forms

end
