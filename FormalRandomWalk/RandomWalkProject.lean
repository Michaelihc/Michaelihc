import Mathlib

open scoped BigOperators

namespace RandomWalkProject

noncomputable section

/-!
This file is the machine-checked companion to the paper. It deliberately
separates project-specific deductions from a small interface of classical
results imported as named axioms in the `Trusted` namespace. Those axioms
are standard path-counting identities, Polya recurrence in dimensions one
and two, and the coupon-collector interpretation of complete-graph cover
time. Every other declaration below is proved by Lean.
-/

/-! ## Exact endpoint laws and recurrence equations -/

def oneDClosed (x0 : Int) (n : Nat) (i : Int) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    if i = x0 + (2 * (k : Int) - (n : Int)) then
      (Nat.choose n k : Real) / (2 : Real) ^ n
    else
      0)

def IsOneDWalkLaw (x0 : Int) (p : Nat -> Int -> Real) : Prop :=
  (forall i, p 0 i = if i = x0 then 1 else 0) /\
  (forall n i, p (n + 1) i = (p n (i - 1) + p n (i + 1)) / 2)

theorem oneDClosed_zero (x0 i : Int) :
    oneDClosed x0 0 i = if i = x0 then 1 else 0 := by
  simp [oneDClosed]

theorem oneD_recurrence_unique
    (x0 : Int) (p q : Nat -> Int -> Real)
    (hp : IsOneDWalkLaw x0 p) (hq : IsOneDWalkLaw x0 q) : p = q := by
  funext n i
  induction n generalizing i with
  | zero =>
      rw [hp.1 i, hq.1 i]
  | succ n ih =>
      rw [hp.2 n i, hq.2 n i, ih (i - 1), ih (i + 1)]

def multinomialWeight4 (n a b c d : Nat) : Real :=
  (Nat.factorial n : Real) /
    ((Nat.factorial a : Real) * (Nat.factorial b : Real) *
      (Nat.factorial c : Real) * (Nat.factorial d : Real) *
      (4 : Real) ^ n)

def twoDClosed (n : Nat) (i j : Int) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun a =>
    Finset.sum (Finset.range (n + 1)) (fun b =>
      Finset.sum (Finset.range (n + 1)) (fun c =>
        Finset.sum (Finset.range (n + 1)) (fun d =>
          if a + b + c + d = n /\
              i = (a : Int) - (b : Int) /\
              j = (c : Int) - (d : Int) then
            multinomialWeight4 n a b c d
          else
            0))))

def IsTwoDWalkLaw (p : Nat -> Int -> Int -> Real) : Prop :=
  (forall i j, p 0 i j = if i = 0 /\ j = 0 then 1 else 0) /\
  (forall n i j,
    p (n + 1) i j =
      (p n (i - 1) j + p n (i + 1) j +
        p n i (j - 1) + p n i (j + 1)) / 4)

theorem twoDClosed_zero (i j : Int) :
    twoDClosed 0 i j = if i = 0 /\ j = 0 then 1 else 0 := by
  simp [twoDClosed, multinomialWeight4]

theorem twoD_recurrence_unique
    (p q : Nat -> Int -> Int -> Real)
    (hp : IsTwoDWalkLaw p) (hq : IsTwoDWalkLaw q) : p = q := by
  funext n i j
  induction n generalizing i j with
  | zero =>
      rw [hp.1 i j, hq.1 i j]
  | succ n ih =>
      rw [hp.2 n i j, hq.2 n i j,
        ih (i - 1) j, ih (i + 1) j,
        ih i (j - 1), ih i (j + 1)]

/-! ## Moment recurrences -/

structure OneDMomentData (x0 : Real) where
  mean : Nat -> Real
  second : Nat -> Real
  mean_zero : mean 0 = x0
  second_zero : second 0 = x0 ^ 2
  mean_step : forall n, mean (n + 1) = mean n
  second_step : forall n, second (n + 1) = second n + 1

def oneDVariance {x0 : Real} (d : OneDMomentData x0) (n : Nat) : Real :=
  d.second n - (d.mean n) ^ 2

theorem oneD_mean_eq_start {x0 : Real} (d : OneDMomentData x0) (n : Nat) :
    d.mean n = x0 := by
  induction n with
  | zero => exact d.mean_zero
  | succ n ih =>
      rw [d.mean_step n, ih]

theorem oneD_second_eq {x0 : Real} (d : OneDMomentData x0) (n : Nat) :
    d.second n = x0 ^ 2 + (n : Real) := by
  induction n with
  | zero => simpa using d.second_zero
  | succ n ih =>
      rw [d.second_step n, ih]
      norm_num [Nat.cast_succ]
      ring

theorem oneD_variance_eq_n {x0 : Real} (d : OneDMomentData x0) (n : Nat) :
    oneDVariance d n = (n : Real) := by
  rw [oneDVariance, oneD_second_eq d n, oneD_mean_eq_start d n]
  ring

structure TwoDMomentData where
  meanX : Nat -> Real
  meanY : Nat -> Real
  msd : Nat -> Real
  meanX_zero : meanX 0 = 0
  meanY_zero : meanY 0 = 0
  msd_zero : msd 0 = 0
  meanX_step : forall n, meanX (n + 1) = meanX n
  meanY_step : forall n, meanY (n + 1) = meanY n
  msd_step : forall n, msd (n + 1) = msd n + 1

theorem twoD_meanX_zero (d : TwoDMomentData) (n : Nat) : d.meanX n = 0 := by
  induction n with
  | zero => exact d.meanX_zero
  | succ n ih =>
      rw [d.meanX_step n, ih]

theorem twoD_meanY_zero (d : TwoDMomentData) (n : Nat) : d.meanY n = 0 := by
  induction n with
  | zero => exact d.meanY_zero
  | succ n ih =>
      rw [d.meanY_step n, ih]

theorem twoD_msd_eq_n (d : TwoDMomentData) (n : Nat) :
    d.msd n = (n : Real) := by
  induction n with
  | zero => simpa using d.msd_zero
  | succ n ih =>
      rw [d.msd_step n, ih]
      norm_num [Nat.cast_succ]

/-! ## Monotone extension: endpoint space, distribution, and covariance -/

abbrev MonotoneEndpoint (n : Nat) := Fin (n + 1)

def monotoneCoordinates (n : Nat) (k : MonotoneEndpoint n) : Nat × Nat :=
  (k.1, n - k.1)

theorem monotone_endpoint_count (n : Nat) :
    Fintype.card (MonotoneEndpoint n) = n + 1 := by
  simp [MonotoneEndpoint]

theorem three_step_sample :
    monotoneCoordinates 3 (0 : Fin 4) = (0, 3) /\
    monotoneCoordinates 3 (1 : Fin 4) = (1, 2) /\
    monotoneCoordinates 3 (2 : Fin 4) = (2, 1) /\
    monotoneCoordinates 3 (3 : Fin 4) = (3, 0) := by
  norm_num [monotoneCoordinates]

def binomialMass (n k : Nat) (p : Real) : Real :=
  (Nat.choose n k : Real) * p ^ k * (1 - p) ^ (n - k)

def monotoneEndpointMass (n : Nat) (p : Real) (x y : Nat) : Real :=
  if x + y = n then binomialMass n x p else 0

theorem monotone_endpoint_mass_formula
    (n x y : Nat) (p : Real) (h : x + y = n) :
    monotoneEndpointMass n p x y =
      (Nat.choose n x : Real) * p ^ x * (1 - p) ^ y := by
  have hy : n - x = y := by omega
  simp [monotoneEndpointMass, binomialMass, h, hy]

def productMass (n : Nat) (p : Real) (z : Nat) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun x =>
    if x * (n - x) = z then binomialMass n x p else 0)

theorem product_distribution_formula (n : Nat) (p : Real) (z : Nat) :
    productMass n p z =
      Finset.sum (Finset.range (n + 1)) (fun x =>
        if x * (n - x) = z then
          (Nat.choose n x : Real) * p ^ x * (1 - p) ^ (n - x)
        else 0) := by
  rfl

def monotoneEX (n : Nat) (p : Real) : Real := (n : Real) * p

def monotoneEY (n : Nat) (p : Real) : Real := (n : Real) * (1 - p)

def monotoneEXY (n : Nat) (p : Real) : Real :=
  (n : Real) * ((n : Real) - 1) * p * (1 - p)

theorem monotone_covariance (n : Nat) (p : Real) :
    monotoneEXY n p - monotoneEX n p * monotoneEY n p =
      -(n : Real) * p * (1 - p) := by
  simp [monotoneEXY, monotoneEX, monotoneEY]
  ring

/-! ## Two-walker extension -/

def independentDifferenceMass
    (n : Nat) (p1 p2 : Real) (x : Int) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun a =>
    Finset.sum (Finset.range (n + 1)) (fun b =>
      if (a : Int) - (b : Int) = x then
        binomialMass n a p1 * binomialMass n b p2
      else
        0))

def fairDifferenceClosed (n : Nat) (x : Int) : Real :=
  Finset.sum (Finset.range (2 * n + 1)) (fun k =>
    if (k : Int) - (n : Int) = x then
      (Nat.choose (2 * n) k : Real) / (2 : Real) ^ (2 * n)
    else
      0)

def correlatedDifferenceMass (n : Nat) (p : Real) (x : Int) : Real :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    if 2 * (k : Int) - (n : Int) = x then binomialMass n k p else 0)

theorem correlated_difference_expectation (n : Nat) (p : Real) :
    2 * ((n : Real) * p) - (n : Real) =
      (n : Real) * (2 * p - 1) := by
  ring

/-! ## Complete graph: stationarity, mixing, and cover time -/

def uniformMass (N : Nat) (_i : Fin N) : Real := 1 / (N : Real)

def CompleteStationary (N : Nat) (pi : Fin N -> Real) : Prop :=
  (Finset.sum Finset.univ pi = 1) /\
  (forall j, pi j = (1 - pi j) / ((N : Real) - 1))

theorem uniform_sums_to_one (N : Nat) (hN : 0 < N) :
    Finset.sum Finset.univ (uniformMass N) = 1 := by
  simp [uniformMass, hN.ne']

theorem complete_uniform_stationary (N : Nat) (hN : 2 <= N) :
    CompleteStationary N (uniformMass N) := by
  constructor
  . exact uniform_sums_to_one N (by omega)
  . intro j
    have hN0 : (N : Real) ≠ 0 := by positivity
    have hNm1 : (N : Real) - 1 ≠ 0 := by
      have h : (2 : Real) <= (N : Real) := by exact_mod_cast hN
      linarith
    simp only [uniformMass]
    field_simp [hN0, hNm1]

theorem complete_stationary_unique
    (N : Nat) (hN : 2 <= N) (pi : Fin N -> Real)
    (hpi : CompleteStationary N pi) : pi = uniformMass N := by
  funext j
  have hN0 : (N : Real) ≠ 0 := by positivity
  have hNm1 : (N : Real) - 1 ≠ 0 := by
    have h : (2 : Real) <= (N : Real) := by exact_mod_cast hN
    linarith
  have hj := hpi.2 j
  have hmul : pi j * ((N : Real) - 1) = 1 - pi j :=
    (eq_div_iff hNm1).mp hj
  simp only [uniformMass]
  apply (eq_div_iff hN0).2
  nlinarith [hmul]

structure CompleteMixingData (N : Nat) where
  tv : Nat -> Real
  tv_zero : tv 0 = ((N : Real) - 1) / (N : Real)
  tv_step : forall t, tv (t + 1) = tv t / ((N : Real) - 1)

theorem complete_tv_exact
    (N : Nat) (d : CompleteMixingData N) (t : Nat) :
    d.tv t = ((N : Real) - 1) / (N : Real) *
      (1 / ((N : Real) - 1)) ^ t := by
  induction t with
  | zero => simpa using d.tv_zero
  | succ t ih =>
      rw [d.tv_step t, ih, pow_succ]
      ring

theorem complete_mixed_if
    (N t : Nat) (d : CompleteMixingData N) (epsilon : Real)
    (h : ((N : Real) - 1) / (N : Real) *
      (1 / ((N : Real) - 1)) ^ t <= epsilon) :
    d.tv t <= epsilon := by
  rw [complete_tv_exact N d t]
  exact h

def harmonic (n : Nat) : Real :=
  Finset.sum (Finset.range n) (fun k => 1 / ((k + 1 : Nat) : Real))

def completeCoverExpectation (N : Nat) : Real :=
  ((N : Real) - 1) * harmonic (N - 1)

theorem completeCoverExpectation_K4 : completeCoverExpectation 4 = 11 / 2 := by
  norm_num [completeCoverExpectation, harmonic]

/-! ## Recurrence and trusted-source interface -/

def IsRecurrent (returnProbability : Real) : Prop := returnProbability = 1

axiom oneDReturnProbability : Real
axiom twoDReturnProbability : Real
axiom completeGraphCoverTime : Nat -> Real

namespace Trusted

axiom oneDClosed_is_law (x0 : Int) : IsOneDWalkLaw x0 (oneDClosed x0)

axiom twoDClosed_is_law : IsTwoDWalkLaw twoDClosed

axiom binomial_mass_normalized (n : Nat) (p : Real) :
  Finset.sum (Finset.range (n + 1)) (fun k => binomialMass n k p) = 1

axiom fair_difference_vandermonde (n : Nat) (x : Int) :
  independentDifferenceMass n (1 / 2) (1 / 2) x = fairDifferenceClosed n x

axiom polya_oneD : IsRecurrent oneDReturnProbability

axiom polya_twoD : IsRecurrent twoDReturnProbability

axiom complete_cover_coupon_collector (N : Nat) :
  completeGraphCoverTime N = completeCoverExpectation N

end Trusted

theorem oneD_closed_form_solves
    (x0 : Int) (p : Nat -> Int -> Real) (hp : IsOneDWalkLaw x0 p) :
    p = oneDClosed x0 :=
  oneD_recurrence_unique x0 p (oneDClosed x0) hp (Trusted.oneDClosed_is_law x0)

theorem twoD_closed_form_solves
    (p : Nat -> Int -> Int -> Real) (hp : IsTwoDWalkLaw p) :
    p = twoDClosed :=
  twoD_recurrence_unique p twoDClosed hp Trusted.twoDClosed_is_law

theorem monotone_mass_normalized (n : Nat) (p : Real) :
    Finset.sum (Finset.range (n + 1)) (fun x => binomialMass n x p) = 1 :=
  Trusted.binomial_mass_normalized n p

theorem fair_difference_formula (n : Nat) (x : Int) :
    independentDifferenceMass n (1 / 2) (1 / 2) x = fairDifferenceClosed n x :=
  Trusted.fair_difference_vandermonde n x

theorem oneD_recurrent : IsRecurrent oneDReturnProbability := Trusted.polya_oneD

theorem twoD_recurrent : IsRecurrent twoDReturnProbability := Trusted.polya_twoD

theorem complete_cover_time_formula (N : Nat) :
    completeGraphCoverTime N = ((N : Real) - 1) * harmonic (N - 1) := by
  rw [Trusted.complete_cover_coupon_collector]
  rfl

theorem complete_cover_time_K4 : completeGraphCoverTime 4 = 11 / 2 := by
  rw [Trusted.complete_cover_coupon_collector]
  exact completeCoverExpectation_K4

end

end RandomWalkProject
