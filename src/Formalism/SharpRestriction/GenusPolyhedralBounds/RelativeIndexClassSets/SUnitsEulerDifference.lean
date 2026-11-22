module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Mathlib
public import Formalism.LogFactorialIndices.StatementIdx
public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
public import Formalism.FilteredPoleLength.ReducedBasisBounds.BetaSesquilinearity

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev WL (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Kl la) (X.Vl la) :=
  X.locK la (X.Msup ka)

def inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N : Submodule (X.Ol la) (X.Vl la)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  N.comap ((WL X ka la).subtype.restrictScalars (X.Ol la))

def MW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) :
    Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Msup ka))

def ThW (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : Submodule (X.Ol la) ↥(WL X ka la) :=
  inW X ka la (X.loc la (X.Theta S ka wL wF T))

attribute [instance] LocDat.iO LocDat.dO LocDat.vO LocDat.aO LocDat.fK LocDat.aOK LocDat.frK LocDat.aKK
  LocDat.aOlK LocDat.st1 LocDat.st2 LocDat.gV LocDat.mKV LocDat.mOV LocDat.st3 LocDat.mKlV LocDat.st4
  LocDat.fK₁ LocDat.aK₁ LocDat.fdK₁ LocDat.sK₁ LocDat.aOK₁ LocDat.st5 LocDat.fι LocDat.gWs LocDat.mWs
  LocDat.rR LocDat.lR LocDat.aR LocDat.hR LocDat.gA LocDat.mRA LocDat.mOA LocDat.sRA LocDat.S_units_euler_difference LocDat.multiplicityBound
  LocDat.fι1 LocDat.dι1

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

def _root_.Formalism.MainNotions.Gaps.T0.InLat (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) ∧
    Formalism.LatticeIndexTer.IsLat (X.Ol la) (X.Kl la) ↥(WL X ka la) (ThW X S ka wL wF T la)

end LocDat

end Formalism.MainNotions.Gaps.T0
