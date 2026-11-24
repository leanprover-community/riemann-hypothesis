module

public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField

namespace GlobalTheory.GeoGraft

variable {D : D7}

def graft (Xg X₀ : DivX D) (iM : ∀ j (c : Xg.Comp j), (X₀.MjH j).V →ₗ[D.what₂.LL] Xg.geo.Fn (Xg.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xg.geo.H0 (Xg.Yv j c) (Xg.Lw j c (DV.kapW D j))) : DivX D :=
  { Xg with
    MjH := X₀.MjH, MjH_good := X₀.MjH_good, jM := X₀.jM, jM_basis := X₀.jM_basis, jM_lat := X₀.jM_lat
    MjLat_sub := X₀.MjLat_sub, jM_metric := X₀.jM_metric
    Qp := X₀.Qp, degreeZero_partial_set_empty := X₀.degreeZero_partial_set_empty, Qp_muAt := X₀.Qp_muAt, Qp_g := X₀.Qp_g
    QPl := X₀.QPl, finQ := X₀.finQ, qv := X₀.qv, qv_gt := X₀.qv_gt, qv_char := X₀.qv_char
    nu := X₀.nu, nu_ne := X₀.nu_ne, nu_abs := X₀.nu_abs, ZQ := X₀.ZQ, quotientLocalValueFirst := X₀.quotientLocalValueFirst, typeDim := X₀.typeDim
    iMj := iM, iMj_mem := hiM
    logLam := X₀.logLam, logLam_base := X₀.logLam_base
    kapR := X₀.kapR, kapR_pos := X₀.kapR_pos, kapR_conj := X₀.kapR_conj }

def Keeps (X X₀ : DivX D) : Prop := ∃ Xg iM hiM, X = graft Xg X₀ iM hiM

def GeoOver (Q : DivX D → Prop) (X₀ : DivX D) : Prop :=
  ∃ (X : DivX D) (inK : X.Lev → ℕ → Prop), Keeps X X₀ ∧ GeoTiedP X inK ∧ Q X

end GlobalTheory.GeoGraft
