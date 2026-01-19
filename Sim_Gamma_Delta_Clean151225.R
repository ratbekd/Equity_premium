# =============================================================================
# BANKING MODEL WITH LIQUIDITY PREMIUM DECOMPOSITION
# Clean, organized version
# =============================================================================

# -----------------------------------------------------------------------------
# 1. LOAD PACKAGES
# -----------------------------------------------------------------------------
library(dplyr)
library(tidyr)
library(ggplot2)
library(patchwork)
library(scales)
library(tibble)
library(zoo)
library(knitr)
library(kableExtra)
`%||%` <- function(a, b) if (is.null(a)) b else a

# -----------------------------------------------------------------------------
# 2. HELPER FUNCTIONS
# -----------------------------------------------------------------------------

# Convert nominal to real rates
to_real <- function(i, Pi) (1 + i) / Pi - 1

# Convert real to nominal rates
to_nom <- function(R, Pi) (1 + R) * Pi - 1

# AR(1) step function
ar1_step <- function(x_prev, rho, mean_bar, sigma, eps) {
  mean_bar * (1 - rho) + rho * x_prev + sigma * eps
}

# Derive zbar from loan rate
zbar_from_RL <- function(RL, gamma) {
  gamma / (gamma + 1 + RL)
}

# Derive beta from equity return
beta_from_RE <- function(RE) {
  1 / (1 + RE)
}

# Derive A from Phi
A_from_Phi <- function(Phi, zbar, gamma) {
  eta <- (1 - zbar)^(1 - gamma) * zbar^gamma
  (Phi * eta)^(1 / (1 - gamma))
}

# Steady-state capital from equity return
k_star_from_RE <- function(RE, alpha, delta, A) {
  (alpha * A / (RE + delta))^(1 / (1 - alpha))
}

# Risk component from moments
Gamma_risk_from_moments <- function(sigma_m, sigma_sstar, rho_ms, Em_bar) {
  sigma_m * sigma_sstar * rho_ms / Em_bar
}

# Zero-profit condition: solve for RB given RS
RB_from_ZP_real <- function(RS, RR, RE, RL, RSigma, rho, theta, kappa) {
  (RS - rho * RR + ((kappa * RE + RSigma - RL) * (1 - rho - theta)) / (1 - kappa)) / theta
}

# Zero-profit condition: solve for RS given RB
RS_from_ZP_real <- function(RB, RR, RE, RL, RSigma, rho, theta, kappa) {
  rho * RR - ((kappa * RE + RSigma - RL) * (1 - rho - theta)) / (1 - kappa) + theta * RB
}

# -----------------------------------------------------------------------------
# 3. CALIBRATION FUNCTION
# -----------------------------------------------------------------------------

calibrate_theta_policy_real <- function(
    theta_target,
    targets = list(
      RS = c(0.001, 0.010),
      RB = c(0.001, 0.012),
      RL = c(0.030, 0.040),
      RE = c(0.070, 0.090)
    ),
    alpha = 0.33, delta = 0.06,
    gamma = 0.60, Phi = 1.00,
    rho = 0.10, kappa = 0.080,
    Pi = NULL, iR = NULL, iSigma = NULL,
    RR = NULL, RSigma = NULL,
    varphi = 0.1,
    grid_n = 101,
    closure = c("solve_RS", "solve_RB"),
    sigma_m = NULL, sigma_sstar = NULL,
    rho_ms = NULL, Em = NULL,
    Delta_bar = 0.0) {

  closure <- match.arg(closure)

  if (theta_target <= 0 || theta_target >= (1 - rho)) {
    stop("theta_target must satisfy 0 < theta < 1 - rho.")
  }

  # Map nominal to real if needed
  if (is.null(RR)) {
    stopifnot(!is.null(Pi), !is.null(iR))
    RR <- to_real(iR, Pi)
  }
  if (is.null(RSigma)) {
    stopifnot(!is.null(Pi), !is.null(iSigma))
    RSigma <- to_real(iSigma, Pi)
  }

  # Compute target midpoints
  RL_star <- mean(targets$RL)
  RE_star <- mean(targets$RE)
  zbar <- zbar_from_RL(RL_star, gamma)
  beta <- beta_from_RE(RE_star)

  # Grid search for feasible RS/RB
  if (closure == "solve_RS") {
    RS_grid <- seq(targets$RS[1], targets$RS[2], length.out = grid_n)
    cand <- lapply(RS_grid, function(RS) {
      RB <- RB_from_ZP_real(RS, RR, RE_star, RL_star, RSigma, rho, theta_target, kappa)
      ok <- (RB >= targets$RB[1] && RB <= targets$RB[2] &&
               RS < RB && RB < RL_star && RL_star < RE_star)
      score <- (RB - mean(targets$RB))^2 + (RS - mean(targets$RS))^2
      list(ok = ok, score = score, RS = RS, RB = RB)
    })
  } else {
    RB_grid <- seq(targets$RB[1], targets$RB[2], length.out = grid_n)
    cand <- lapply(RB_grid, function(RB) {
      RS <- RS_from_ZP_real(RB, RR, RE_star, RL_star, RSigma, rho, theta_target, kappa)
      ok <- (RS >= targets$RS[1] && RS <= targets$RS[2] &&
               RS < RB && RB < RL_star && RL_star < RE_star)
      score <- (RB - mean(targets$RB))^2 + (RS - mean(targets$RS))^2
      list(ok = ok, score = score, RS = RS, RB = RB)
    })
  }

  feas <- cand[vapply(cand, `[[`, logical(1), "ok")]
  if (!length(feas)) {
    stop("No feasible solution: adjust theta_target or widen target bands.")
  }

  best <- feas[[which.min(vapply(feas, `[[`, numeric(1), "score"))]]
  RS <- as.numeric(best$RS)
  RB <- as.numeric(best$RB)
  RL <- RL_star
  RE <- RE_star

  # Risk decomposition
  if (any(sapply(list(sigma_m, sigma_sstar, rho_ms, Em), is.null))) {
    stop("Must pass sigma_m, sigma_sstar, rho_ms, Em for risk decomposition.")
  }
  Gamma_risk_bar <- Gamma_risk_from_moments(sigma_m, sigma_sstar, rho_ms, Em)
  Gamma_bar <- -Delta_bar + Gamma_risk_bar

  # LP decomposition at steady state
  LP_carry <- (1 - theta_target) * RB
  LP_reserve <- -rho * RR
  LP_wedge <- ((1 - rho - theta_target) / (1 - kappa)) * (kappa * RE + RSigma - RL)
  LP_real <- LP_carry + LP_reserve + LP_wedge + Delta_bar - Gamma_risk_bar

  lp_parts <- c(
    carry = LP_carry,
    reserve = LP_reserve,
    wedge = LP_wedge,
    Delta = Delta_bar,
    Gamma_risk = -Gamma_risk_bar
  )

  # Quantities
  A <- A_from_Phi(Phi, zbar, gamma)
  k <- k_star_from_RE(RE, alpha, delta, A)
  y <- A * k^alpha
  z <- (zbar / (1 - zbar)) * y
  L <- z
  D <- (1 - kappa) * L / (1 - rho - theta_target)
  B <- theta_target * D
  Rres <- rho * D
  Ebank <- kappa * L
  c_unc <- y - delta * k
  c <- min(c_unc, varphi * D)
  CIA_binds <- (c < c_unc)

  quantities <- c(
    k = k, y = y, z = z, L = L, D = D, B = B,
    Rres = Rres, Ebank = Ebank,
    c_unc = c_unc, c = c, CIA_binds = as.numeric(CIA_binds)
  )

  list(
    calibration = list(
      theta = theta_target,
      zbar = zbar,
      beta = beta,
      A = A,
      RS = RS, RB = RB, RL = RL, RE = RE,
      Pi = Pi,
      rho = rho,
      kappa = kappa,
      RR = RR,
      RSigma = RSigma,
      Gamma = Gamma_bar,
      Gamma_risk = Gamma_risk_bar,
      Delta_bar = Delta_bar,
      sigma_m = sigma_m,
      sigma_sstar = sigma_sstar,
      rho_ms = rho_ms,
      Em = Em
    ),
    rates_real = c(RS = RS, RB = RB, RL = RL, RE = RE),
    quantities = quantities,
    lp = list(LP_real = LP_real, components = lp_parts),
    ordering_ok = (RS < RB && RB < RL && RL < RE)
  )
}

# -----------------------------------------------------------------------------
# 4. SIMULATION FUNCTION
# -----------------------------------------------------------------------------

simulate_path_real <- function(
    T,
    theta_bar, RSigma, RR, RL_calib, RE_calib, RB_calib,
    zbar, beta, alpha, delta, gamma, A_bar,
    rho_A = 0.95, sigma_A = 0.01,
    rho_theta = 0.6, sigma_theta = 0.00,
    rho_Gamma = 0.90, sigma_Gamma = 0.00,
    Gamma_risk_bar,
    rho_Delta = 0.90, sigma_Delta = 0.00,
    Delta_bar,
    rho_req, kappa,
    varphi = 0.40, Pi = 1.02,
    bond_closure = c("const", "SDF", "AR1", "ZP_RB"),
    RB_rho = 0.9, RB_sigma = 0.001,
    RS_anchor = NULL,
    lambda_RS = 0.3,
    k0 = NULL, A0 = A_bar, theta0 = theta_bar,
    Gamma_risk0 = Gamma_risk_bar,
    Delta0 = Delta_bar,
    seed = 1L,
    logA = TRUE) {

  bond_closure <- match.arg(bond_closure)
  set.seed(seed)

  # Sanity checks
  if (!is.numeric(A_bar) || length(A_bar) != 1 || !is.finite(A_bar)) {
    stop("A_bar must be a finite numeric scalar.")
  }
  if (logA && A_bar <= 0) {
    stop("A_bar must be > 0 when logA = TRUE.")
  }

  # Compute RS_anchor if not provided
  if (is.null(RS_anchor)) {
    RS_anchor <- RS_from_ZP_real(
      RB = RB_calib, RR = RR, RE = RE_calib, RL = RL_calib,
      RSigma = RSigma, rho = rho_req, theta = theta_bar, kappa = kappa
    )
  }

  # Initial capital
  if (is.null(k0)) {
    k0 <- k_star_from_RE(RE_calib, alpha, delta, A_bar)
  }

  # Preallocate output
  out <- data.frame(
    t = 0:(T - 1),
    A = NA_real_, theta = NA_real_,
    Gamma_risk_t = NA_real_, Delta_t = NA_real_,
    k = NA_real_, y = NA_real_, z = NA_real_, L = NA_real_,
    D = NA_real_, B = NA_real_, Rres = NA_real_, Ebank = NA_real_,
    c_unc = NA_real_, c = NA_real_, CIA_binds = NA,
    RL = NA_real_, RE = NA_real_, RR = NA_real_,
    RB = NA_real_, RS = NA_real_,
    iL = NA_real_, iE = NA_real_, iR = NA_real_,
    iB = NA_real_, iS = NA_real_,
    LP = NA_real_, LP_carry = NA_real_, LP_reserve = NA_real_,
    LP_wedge = NA_real_, LP_risk = NA_real_
  )

  # Initialize states
  k_t <- k0
  A_t <- A0
  theta_t <- theta0
  RB_t <- RB_calib
  RB_prev <- RB_calib
  Gamma_risk_t <- Gamma_risk0
  Delta_t <- Delta0

  # Main simulation loop
  for (idx in 1:T) {
    t <- idx - 1

    # Generate shocks
    epsA <- rnorm(1)
    epsTh <- rnorm(1)
    epsG <- rnorm(1)
    epsD <- rnorm(1)

    # Update state variables with AR(1) processes
    if (logA) {
      A_t <- exp(ar1_step(log(A_t), rho_A, log(A_bar), sigma_A, epsA))
    } else {
      A_t <- pmax(ar1_step(A_t, rho_A, A_bar, sigma_A, epsA),
                  .Machine$double.eps)
    }

    theta_t <- ar1_step(theta_t, rho_theta, theta_bar, sigma_theta, epsTh)
    Gamma_risk_t <- ar1_step(Gamma_risk_t, rho_Gamma, Gamma_risk_bar, sigma_Gamma, epsG)
    Delta_t <- ar1_step(Delta_t, rho_Delta, Delta_bar, sigma_Delta, epsD)

    if (theta_t >= 1 - rho_req) {
      stop("theta_t violates 1 - rho_req - theta_t > 0.")
    }

    # Technology and working capital
    y_t <- A_t * k_t^alpha
    z_t <- (zbar / (1 - zbar)) * y_t
    L_t <- z_t

    # Returns
    RL_t <- RL_calib
    RE_t <- alpha * A_t * k_t^(alpha - 1) - delta

    # Bond/deposit closure
    if (bond_closure == "const") {
      RB_t <- RB_calib
      RS_t <- RS_from_ZP_real(RB_t, RR, RE_t, RL_t, RSigma, rho_req, theta_t, kappa)
    } else if (bond_closure == "SDF") {
      RB_t <- 1 / beta - 1
      RS_t <- RS_from_ZP_real(RB_t, RR, RE_t, RL_t, RSigma, rho_req, theta_t, kappa)
    } else if (bond_closure == "AR1") {
      RB_t <- ar1_step(RB_t, RB_rho, RB_calib, RB_sigma, rnorm(1))
      RS_t <- RS_from_ZP_real(RB_t, RR, RE_t, RL_t, RSigma, rho_req, theta_t, kappa)
    } else if (bond_closure == "ZP_RB") {
      if (t == 0) {
        RS_t <- RS_anchor
      } else {
        RS_t <- RS_anchor + lambda_RS * (RB_prev - RB_calib)
      }
      RB_t <- RB_from_ZP_real(RS_t, RR, RE_t, RL_t, RSigma, rho_req, theta_t, kappa)
    }

    # Bank balance sheet
    denom <- (1 - rho_req - theta_t)
    D_t <- (1 - kappa) * L_t / denom
    B_t <- theta_t * D_t
    Rres_t <- rho_req * D_t
    Ebank_t <- kappa * L_t

    # CIA and capital accumulation
    c_unc_t <- y_t - delta * k_t
    c_t <- min(c_unc_t, varphi * D_t)
    CIA_bind <- (c_t < c_unc_t)
    k_next <- (1 - delta) * k_t + (y_t - c_t)

    # LP components
    LP_carry_t <- (1 - theta_t) * RB_t
    LP_reserve_t <- -rho_req * RR
    LP_wedge_t <- ((1 - rho_req - theta_t) / (1 - kappa)) *
      (kappa * RE_t + RSigma - RL_t)
    LP_risk_t <- -Gamma_risk_t

    LP_t <- LP_carry_t + LP_reserve_t + LP_wedge_t + Delta_t + LP_risk_t

    # Store results
    out[idx, ] <- list(
      t, A_t, theta_t, Gamma_risk_t, Delta_t,
      k_t, y_t, z_t, L_t,
      D_t, B_t, Rres_t, Ebank_t,
      c_unc_t, c_t, CIA_bind,
      RL_t, RE_t, RR, RB_t, RS_t,
      to_nom(RL_t, Pi), to_nom(RE_t, Pi), to_nom(RR, Pi),
      to_nom(RB_t, Pi), to_nom(RS_t, Pi),
      LP_t, LP_carry_t, LP_reserve_t, LP_wedge_t, LP_risk_t
    )

    # Update states
    k_t <- k_next
    RB_prev <- RB_t
  }

  out
}

# -----------------------------------------------------------------------------
# 5. PLOTTING FUNCTIONS
# -----------------------------------------------------------------------------

plot_rates <- function(sim, bands = list(
  RS = c(0.001, 0.010),
  RB = c(0.001, 0.012),
  RL = c(0.030, 0.040),
  RE = c(0.070, 0.090)
)) {
  df <- sim %>%
    transmute(t, RS, RB, RL, RE) %>%
    pivot_longer(-t, names_to = "rate", values_to = "value")

  banddf <- tibble(
    rate = rep(names(bands), each = 2),
    bound = rep(c("lo", "hi"), times = length(bands)),
    val = unlist(bands)
  ) %>%
    pivot_wider(names_from = "bound", values_from = "val")

  ggplot(df, aes(t, value, color = rate)) +
    geom_hline(data = banddf, aes(yintercept = lo), linetype = 3, alpha = .6) +
    geom_hline(data = banddf, aes(yintercept = hi), linetype = 3, alpha = .6) +
    geom_line(linewidth = 0.9) +
    scale_y_continuous(labels = percent_format(accuracy = 0.1)) +
    labs(title = "Real Rates vs Target Bands", y = "Rate (real)", x = "t") +
    theme_minimal(base_size = 12) +
    theme(legend.position = "bottom")
}

plot_spreads <- function(sim) {
  df <- sim %>%
    transmute(
      t,
      `RB - RS` = RB - RS,
      `RL - RB` = RL - RB,
      `RE - RB` = RE - RB
    ) %>%
    pivot_longer(-t, names_to = "spread", values_to = "value")

  ggplot(df, aes(t, value, color = spread)) +
    geom_hline(yintercept = 0, color = "grey60") +
    geom_line(linewidth = 0.9) +
    scale_y_continuous(labels = percent_format(accuracy = 0.1)) +
    labs(title = "Spreads", y = "Spread (real)", x = "t") +
    theme_minimal(base_size = 12) +
    theme(legend.position = "bottom")
}

plot_lp_decomposition <- function(sim, as_percent = TRUE) {
  # Build component data
  lp_df <- sim %>%
    transmute(
      t = t,
      `Bond–carry term` = LP_carry,
      `Reserve drag` = LP_reserve,
      `Regulatory wedge` = LP_wedge,
      `Pricing wedge (+Δ_t)` = Delta_t,
      `Risk term (−Γ_risk,t)` = -Gamma_risk_t
    )

  # Long format for stacked area
  lp_long <- lp_df %>%
    pivot_longer(cols = -t, names_to = "component", values_to = "value") %>%
    mutate(
      component = factor(
        component,
        levels = c(
          "Bond–carry term",
          "Reserve drag",
          "Regulatory wedge",
          "Pricing wedge (+Δ_t)",
          "Risk term (−Γ_risk,t)"
        )
      )
    )

  # Total LP for overlay
  lp_total <- tibble(t = sim$t, LP = sim$LP)

  p <- ggplot(lp_long, aes(x = t, y = value, fill = component)) +
    geom_area(position = "stack", alpha = 0.85) +
    geom_line(
      data = lp_total,
      aes(x = t, y = LP),
      inherit.aes = FALSE,
      linewidth = 0.8,
      color = "black"
    ) +
    labs(
      title = "Liquidity Premium Decomposition",
      x = "Periods",
      y = if (as_percent) "Real rate (percent)" else "Real rate",
      fill = "Component"
    ) +
    theme_minimal(base_size = 12) +
    theme(
      legend.position = "bottom",
      legend.text = element_text(size = 11),
      legend.title = element_text(size = 11)
    )

  if (as_percent) {
    p <- p + scale_y_continuous(labels = percent_format(accuracy = 0.1))
  }

  p
}

plot_quantities <- function(sim, norm = c("first", "mean")) {
  norm <- match.arg(norm)
  baseK <- if (norm == "first") sim$k[1] else mean(sim$k)
  baseY <- if (norm == "first") sim$y[1] else mean(sim$y)
  baseD <- if (norm == "first") sim$D[1] else mean(sim$D)
  baseL <- if (norm == "first") sim$L[1] else mean(sim$L)

  df <- sim %>%
    transmute(
      t,
      `k/k₀` = k / baseK,
      `y/y₀` = y / baseY,
      `D/D₀` = D / baseD,
      `L/L₀` = L / baseL,
      CIA_binds = CIA_binds %in% c(TRUE, 1)
    ) %>%
    pivot_longer(c(`k/k₀`, `y/y₀`, `D/D₀`, `L/L₀`),
                 names_to = "var", values_to = "value")

  p <- ggplot(df, aes(t, value, color = var)) +
    geom_line(linewidth = 0.9) +
    labs(title = "Quantities (normalized)", y = "Index", x = "t") +
    theme_minimal(base_size = 12) +
    theme(legend.position = "bottom")

  if (any(sim$CIA_binds %in% c(TRUE, 1))) {
    shade <- sim %>%
      filter(CIA_binds %in% c(TRUE, 1)) %>%
      transmute(xmin = t - 0.5, xmax = t + 0.5, ymin = -Inf, ymax = Inf)
    p <- p + geom_rect(
      data = shade, inherit.aes = FALSE,
      aes(xmin = xmin, xmax = xmax, ymin = ymin, ymax = ymax),
      fill = "grey90", alpha = 0.6
    )
  }
  p
}

plot_dashboard <- function(sim, bands = NULL) {
  p1 <- plot_rates(sim, bands %||% list(
    RS = c(0.001, 0.010), RB = c(0.001, 0.012),
    RL = c(0.030, 0.040), RE = c(0.070, 0.090)
  ))
  p2 <- plot_spreads(sim)
  wrap_plots(p1, p2, ncol = 2)
}

# -----------------------------------------------------------------------------
# 6. SUMMARY FUNCTIONS
# -----------------------------------------------------------------------------

print_Gamma_decomposition <- function(cal, name = "Baseline") {
  Gamma_total <- cal$Gamma
  Gamma_risk <- cal$Gamma_risk
  Delta_bar <- cal$Delta_bar

  cat("---- Gamma decomposition (", name, ") ----\n", sep = "")
  cat(sprintf("Γ (total)      : % .6f  (%.2f bps)\n",
              Gamma_total, Gamma_total * 1e4))

  if (!is.null(Delta_bar) && is.finite(Delta_bar)) {
    cat(sprintf("Δ (pricing)    : % .6f  (%.2f bps)\n",
                Delta_bar, Delta_bar * 1e4))
  } else {
    cat("Δ (pricing)    : NA\n")
  }

  if (!is.null(Gamma_risk) && is.finite(Gamma_risk)) {
    cat(sprintf("Γ_risk (cov)   : % .6f  (%.2f bps)\n",
                Gamma_risk, Gamma_risk * 1e4))
  } else {
    cat("Γ_risk (cov)   : NA\n")
  }

  if (is.finite(Gamma_total) && is.finite(Delta_bar) && is.finite(Gamma_risk)) {
    diff <- Gamma_total - (-Delta_bar + Gamma_risk)
    cat(sprintf("Check Γ - (-Δ+Γ_risk): % .2e\n", diff))
  }

  cat("----------------------------------------\n")
}

make_summary_table <- function(res, sim) {
  rates_cal <- res$rates_real

  rates_mean <- c(
    RS = mean(sim$RS), RB = mean(sim$RB),
    RL = mean(sim$RL), RE = mean(sim$RE)
  )

  rates_sd <- c(
    RS = sd(sim$RS), RB = sd(sim$RB),
    RL = sd(sim$RL), RE = sd(sim$RE)
  )

  tab_summary_sim <- data.frame(
    Asset = c("Deposits", "Bills/Bonds", "Loans", "Equity"),
    Symbol = c("$R^s$", "$R^B$", "$R^L$", "$R^E$"),
    Calibrated = 100 * as.numeric(rates_cal[c("RS", "RB", "RL", "RE")]),
    Mean.sim = 100 * as.numeric(rates_mean[c("RS", "RB", "RL", "RE")]),
    Std.dev.sim = 100 * as.numeric(rates_sd[c("RS", "RB", "RL", "RE")])
  )

  kable(
    tab_summary_sim,
    format = "latex",
    booktabs = TRUE,
    digits = c(NA, NA, 3, 2, 2),
    col.names = c("Asset", "Symbol", "Calibrated",
                  "Mean (sim.)", "Std.\\ dev.\\ (sim.)"),
    caption = "Real rates of return: calibrated targets and simulated moments (annual, percent).",
    label = "summary_sim"
  )
}

# -----------------------------------------------------------------------------
# 7. EXAMPLE USAGE
# -----------------------------------------------------------------------------

# Run calibration
res <- calibrate_theta_policy_real(
  theta_target = 0.50,
  targets = list(
    RS = c(0.001, 0.010),
    RB = c(0.001, 0.012),
    RL = c(0.030, 0.040),
    RE = c(0.070, 0.090)
  ),
  alpha = 0.33, delta = 0.06, gamma = 0.600, Phi = 1.00,
  rho = 0.10, kappa = 0.10,
  Pi = 1.02, iR = 0.000, iSigma = 0.05,
  varphi = 0.0510,
  grid_n = 101,
  closure = "solve_RB",
  sigma_m = 0.05, sigma_sstar = 0.04,
  rho_ms = 0.6, Em = 0.99,
  Delta_bar = 0.063
)

cal <- res$calibration

# Extract calibration
cal <- res$calibration

# Print decomposition
print_Gamma_decomposition(cal, "θ-policy calibration")

# Run simulation
sim <- simulate_path_real(
  T = 200,
  theta_bar = cal$theta,
  RSigma = cal$RSigma,
  RR = cal$RR,
  RL_calib = res$rates_real["RL"],
  RE_calib = res$rates_real["RE"],
  RB_calib = res$rates_real["RB"],
  zbar = cal$zbar,
  beta = cal$beta,
  alpha = 0.33, delta = 0.06, gamma = 0.60,
  A_bar = cal$A,
  rho_A = 0.94, sigma_A = 0.01,
  rho_theta = 0.60, sigma_theta = 0.00,
  rho_Gamma = 0.90, sigma_Gamma = 0.0002,
  Gamma_risk_bar = cal$Gamma_risk,
  rho_Delta = 0.90, sigma_Delta = 0.0002,
  Delta_bar = cal$Delta_bar,
  rho_req = cal$rho,
  kappa = cal$kappa,
  varphi = 0.65,
  Pi = if (is.null(cal$Pi)) 1.02 else cal$Pi,
  bond_closure = "ZP_RB",
  RS_anchor = cal$RS,
  lambda_RS = 0.3,
  seed = 123
)

# Trim burn-in period
sim_trim <- sim %>% filter(t >= 10)

# Generate plots
p_dashboard <- plot_dashboard(sim_trim)
print(p_dashboard)

p_lp <- plot_lp_decomposition(sim_trim, as_percent = TRUE)
print(p_lp)

# Print summary table
make_summary_table(res, sim_trim)

# Calculate LP moments
lp_moments <- sim_trim %>%
  summarise(
    mean_LP = mean(LP),
    sd_LP = sd(LP),
    mean_carry = mean(LP_carry),
    sd_carry = sd(LP_carry),
    mean_reserve = mean(LP_reserve),
    sd_reserve = sd(LP_reserve),
    mean_wedge = mean(LP_wedge),
    sd_wedge = sd(LP_wedge),
    mean_Delta = mean(Delta_t),
    sd_Delta = sd(Delta_t),
    mean_Gammar = mean(LP_risk),
    sd_Gammar = sd(LP_risk)
  )

print(lp_moments)


# -----------------------------------------------------------------------------
# 8. IMPULSE RESPONSE FUNCTIONS
# -----------------------------------------------------------------------------

# IRF parameters
H_irf <- 100
sigma_A_irf <- 0.01
sigma_theta_irf <- 0.01

# --- Technology Shock IRF ---

# Baseline (no shock)
sim0_A <- simulate_path_real(
  T = H_irf,
  theta_bar = cal$theta,
  RSigma = cal$RSigma,
  RR = cal$RR,
  RL_calib = res$rates_real["RL"],
  RE_calib = res$rates_real["RE"],
  RB_calib = res$rates_real["RB"],
  zbar = cal$zbar,
  beta = cal$beta,
  alpha = 0.33, delta = 0.06, gamma = 0.60,
  A_bar = cal$A,
  rho_A = 0.94, sigma_A = 0.00,
  rho_theta = 0.60, sigma_theta = 0.00,
  rho_Gamma = 0.90, sigma_Gamma = 0.00,
  Gamma_risk_bar = cal$Gamma_risk,
  rho_Delta = 0.90, sigma_Delta = 0.00,
  Delta_bar = cal$Delta_bar,
  rho_req = cal$rho,
  kappa = cal$kappa,
  varphi = 0.65,
  Pi = if (is.null(cal$Pi)) 1.02 else cal$Pi,
  bond_closure = "ZP_RB",
  RS_anchor = cal$RS,
  lambda_RS = 0.3,
  A0 = cal$A,
  theta0 = cal$theta,
  seed = 123
)

# With technology shock
A0_shock <- cal$A * exp(sigma_A_irf)

sim_Ashock <- simulate_path_real(
  T = H_irf,
  theta_bar = cal$theta,
  RSigma = cal$RSigma,
  RR = cal$RR,
  RL_calib = res$rates_real["RL"],
  RE_calib = res$rates_real["RE"],
  RB_calib = res$rates_real["RB"],
  zbar = cal$zbar,
  beta = cal$beta,
  alpha = 0.33, delta = 0.06, gamma = 0.60,
  A_bar = cal$A,
  rho_A = 0.94, sigma_A = 0.00,
  rho_theta = 0.60, sigma_theta = 0.00,
  rho_Gamma = 0.90, sigma_Gamma = 0.00,
  Gamma_risk_bar = cal$Gamma_risk,
  rho_Delta = 0.90, sigma_Delta = 0.00,
  Delta_bar = cal$Delta_bar,
  rho_req = cal$rho,
  kappa = cal$kappa,
  varphi = 0.65,
  Pi = if (is.null(cal$Pi)) 1.02 else cal$Pi,
  bond_closure = "ZP_RB",
  RS_anchor = cal$RS,
  lambda_RS = 0.3,
  A0 = A0_shock,
  theta0 = cal$theta,
  seed = 123
)

# Compute IRF
irf_A <- data.frame(
  t = sim0_A$t,
  y = sim_Ashock$y - sim0_A$y,
  RN = sim_Ashock$RE - sim0_A$RE,
  RB = sim_Ashock$RB - sim0_A$RB,
  RS = sim_Ashock$RS - sim0_A$RS,
  EP = (sim_Ashock$RE - sim_Ashock$RB) - (sim0_A$RE - sim0_A$RB)
)

# Plot technology shock IRF
irf_A_long <- irf_A %>%
  pivot_longer(cols = -t, names_to = "var", values_to = "value")

p_irf_A <- ggplot(irf_A_long, aes(x = t, y = value, colour = var)) +
  geom_hline(yintercept = 0, colour = "grey60") +
  geom_line(linewidth = 1.0) +
  labs(
    title = "IRFs to 1-s.d. Technology Shock (A_t)",
    x = "Periods",
    y = "Deviation from baseline",
    colour = "Variable"
  ) +
  theme_minimal() +
  theme(legend.position = "bottom")

print(p_irf_A)

# --- Policy (Theta) Shock IRF ---

# Baseline (no shock)
sim0_theta <- simulate_path_real(
  T = H_irf,
  theta_bar = cal$theta,
  RSigma = cal$RSigma,
  RR = cal$RR,
  RL_calib = res$rates_real["RL"],
  RE_calib = res$rates_real["RE"],
  RB_calib = res$rates_real["RB"],
  zbar = cal$zbar,
  beta = cal$beta,
  alpha = 0.33, delta = 0.06, gamma = 0.60,
  A_bar = cal$A,
  rho_A = 0.94, sigma_A = 0.00,
  rho_theta = 0.50, sigma_theta = 0.00,
  rho_Gamma = 0.90, sigma_Gamma = 0.00,
  Gamma_risk_bar = cal$Gamma_risk,
  rho_Delta = 0.90, sigma_Delta = 0.00,
  Delta_bar = cal$Delta_bar,
  rho_req = cal$rho,
  kappa = cal$kappa,
  varphi = 0.65,
  Pi = if (is.null(cal$Pi)) 1.02 else cal$Pi,
  bond_closure = "ZP_RB",
  RS_anchor = cal$RS,
  lambda_RS = 0.3,
  A0 = cal$A,
  theta0 = cal$theta,
  seed = 123
)

# With theta shock
theta0_shock <- cal$theta + sigma_theta_irf

sim_theta_shock <- simulate_path_real(
  T = H_irf,
  theta_bar = cal$theta,
  RSigma = cal$RSigma,
  RR = cal$RR,
  RL_calib = res$rates_real["RL"],
  RE_calib = res$rates_real["RE"],
  RB_calib = res$rates_real["RB"],
  zbar = cal$zbar,
  beta = cal$beta,
  alpha = 0.33, delta = 0.06, gamma = 0.60,
  A_bar = cal$A,
  rho_A = 0.94, sigma_A = 0.00,
  rho_theta = 0.50, sigma_theta = 0.00,
  rho_Gamma = 0.90, sigma_Gamma = 0.00,
  Gamma_risk_bar = cal$Gamma_risk,
  rho_Delta = 0.90, sigma_Delta = 0.00,
  Delta_bar = cal$Delta_bar,
  rho_req = cal$rho,
  kappa = cal$kappa,
  varphi = 0.65,
  Pi = if (is.null(cal$Pi)) 1.02 else cal$Pi,
  bond_closure = "ZP_RB",
  RS_anchor = cal$RS,
  lambda_RS = 0.3,
  A0 = cal$A,
  theta0 = theta0_shock,
  seed = 123
)

# Compute IRF
irf_theta <- data.frame(
  t = sim0_theta$t,
  RB = sim_theta_shock$RB - sim0_theta$RB,
  RS = sim_theta_shock$RS - sim0_theta$RS,
  RN = sim_theta_shock$RE - sim0_theta$RE,
  EP = (sim_theta_shock$RE - sim_theta_shock$RB) - (sim0_theta$RE - sim0_theta$RB),
  y = sim_theta_shock$y - sim0_theta$y
)

# Plot theta shock IRF
irf_theta_long <- irf_theta %>%
  pivot_longer(cols = -t, names_to = "Variable", values_to = "value")

p_irf_theta <- ggplot(irf_theta_long, aes(x = t, y = value, colour = Variable)) +
  geom_hline(yintercept = 0, colour = "grey60") +
  geom_line(linewidth = 1.0) +
  labs(
    title = "IRFs to 1-s.d. Policy Bond Share Shock (θ_t)",
    x = "Periods",
    y = "Deviation from baseline"
  ) +
  theme_minimal() +
  theme(legend.position = "bottom")

print(p_irf_theta)

###=============================================================
## Example use of Summary functions
##==============================================================
## 1. Calibrated real rates (from theta-policy calibration)
##    names should be: RS = deposits, RB = bonds, RL = loans, RE = equity
rates_cal <- res$rates_real

## 2. Simulated means and std devs (real)
rates_mean <- c(
  RS = mean(sim$RS),
  RB = mean(sim$RB),
  RL = mean(sim$RL),
  RE = mean(sim$RE)
)

rates_sd <- c(
  RS = sd(sim$RS),
  RB = sd(sim$RB),
  RL = sd(sim$RL),
  RE = sd(sim$RE)
)

## 3. Assemble table (×100 to get annual percent)
tab_summary_sim <- data.frame(
  Asset        = c("Deposits", "Bills/Bonds", "Loans", "Equity"),
  Symbol       = c("$R^s$", "$R^B$", "$R^L$", "$R^E$"),
  Calibrated   = 100 * as.numeric(rates_cal[c("RS","RB","RL","RE")]),
  Mean.sim     = 100 * as.numeric(rates_mean[c("RS","RB","RL","RE")]),
  Std.dev.sim  = 100 * as.numeric(rates_sd[c("RS","RB","RL","RE")])
)



print_Gamma_decomposition(cal, "θ-policy calibration")
## LaTeX table (Table 3)
make_summary_table(res, sim)


## 4. LaTeX output:Real rates of return: calibrated targets and simulated moments (annual, percent)
kable(
  tab_summary_sim,
  format   = "latex",
  booktabs = TRUE,
  digits   = c(NA, NA, 3, 2, 2),  # 0.126, 0.10, 0.10 etc.
  col.names = c("Asset", "Symbol",
                "Calibrated", "Mean (sim.)", "Std.\\ dev.\\ (sim.)"),
  caption  = "Real rates of return: calibrated targets and simulated moments (annual, percent).",
  label    = "summary_sim"
)

# -----------------------------------------------------------------------------
# 7. EXAMPLE USAGE
# -----------------------------------------------------------------------------
# Run calibration
res <- calibrate_theta_policy_real(
  theta_target = 0.50,
  targets = list(
    RS = c(0.001, 0.010),
    RB = c(0.001, 0.012),
    RL = c(0.030, 0.040),
    RE = c(0.070, 0.090)
  ),
  alpha = 0.33, delta = 0.06, gamma = 0.600, Phi = 1.00,
  rho = 0.10, kappa = 0.10,
  Pi = 1.02, iR = 0.000, iSigma = 0.05,
  varphi = 0.0510,
  grid_n = 101,
  closure = "solve_RB",
  sigma_m = 0.05, sigma_sstar = 0.04,
  rho_ms = 0.6, Em = 0.99,
  Delta_bar = 0.063
)

# -----------------------------------------------------------------------------
# 9. EQUITY PREMIUM COMPARISON (Optional Example)
# -----------------------------------------------------------------------------
## first 97 obs from the simulated rates
rates_97 <- sim[1:97, ]      # RS, RB, RL, RE
HEP$SHEP=NA
## first 97 obs from X (assume X is at least length 97)
X_97 <- HEP$`B-E`[1:97]
HEP$time <- HEP$`Year`[1:97]
HEP$SHEP[1:78] <- 0.061

# HEP$time2 <- time^2
# HEP$time3 <- time^3
# HEP$time4 <- time^4
Average_HEP <- predict(lm(X_97~time,data=HEP))
## 3. 10-period moving average of X (right-aligned)
X_97_ma <- stats::filter(X_97, rep(1/25, 25), sides = 1)
X_97_ma <- as.numeric(X_97_ma)  # drop ts attribute
## put everything in one data frame
plot_df <- data.frame(
  t  = 1:97,
  #RS = rates_97$RE-rates_97$RS,
  Equity_Bond_Spread_simulated = rates_97$RE-rates_97$RB,
  #Equity_Loan_Spread = rates_97$RE-rates_97$RL,
  Aver_HEP_Damodaran=mean(X_97),
  #HEP_MA = X_97_ma,
  Aver_HEP_Sigel=HEP$SHEP
)


## 5. Long format for ggplot
plot_df_long <- plot_df |>
  pivot_longer(cols = -t, names_to = "series", values_to = "value")

ggplot(plot_df_long, aes(x = t, y = value, colour = series)) +
  geom_line(linewidth = 1.3) +
  labs(x = "Years", y = "Real return", colour = "Series") +
  theme_minimal() +
  theme(
    legend.position = "bottom",
    legend.text  = element_text(size = 12),  # labels
    legend.title = element_text(size = 12)   # "Series"
  )

# After running calibration and simulation:
make_lp_decomposition_table(res, sim_trim)
# cal <- res$calibration
#
# B-E`[1:n_periods]
#
#   plot_df <- data.frame(
#     t = 1:n_periods,
#     Simulated_EP = rates_n$RE - rates_n$RB,
#     Historical_Mean = mean(X_n, na.rm = TRUE),
#     Historical_MA = stats::filter(X_n, rep(1/25, 25), sides = 1)
#   )
#
#   plot_df_long <- plot_df %>%
#     pivot_longer(cols = -t, names_to = "series", values_to = "value")
#
#   ggplot(plot_df_long, aes(x = t, y = value, colour = series)) +
#     geom_line(linewidth = 1.3) +
#     labs(x = "Years", y = "Real return", colour = "Series") +
#     theme_minimal() +
#     theme(
#       legend.position = "bottom",
#       legend.text = element_text(size = 12),
#       legend.title = element_text(size = 12)
#     )
# }


##=============================================================================
##   Tables

## 1. Extract real rates from your calibration object
##    (RS = deposits, RB = bonds, RL = loans, RE = equity ≡ R^N)
rates <- res$rates_real
RS <- as.numeric(rates["RS"])
RB <- as.numeric(rates["RB"])
RL <- as.numeric(rates["RL"])
RN <- as.numeric(rates["RE"])  # notation: R^N in the paper

## 2. Check ordering and compute spreads
ordering_ok <- (RS < RB) & (RB < RL) & (RL < RN)

tab_order <- data.frame(
  `Check / spread` = c(
    "Ordering $R^s<R^B<R^L<R^N$",
    "Spread $R^N - R^B$",
    "Spread $R^B - R^s$",
    "Spread $R^L - R^B$",
    "Spread $R^N - R^L$"
  ),
  Value = c(
    if (ordering_ok) "\\textbf{Yes}" else "\\textbf{No}",
    sprintf("%.4f", RN - RB),
    sprintf("%.4f", RB - RS),
    sprintf("%.4f", RL - RB),
    sprintf("%.4f", RN - RL)
  ),
  check.names = FALSE
)




##=============================================================================
## LaTeX table (Table 3)
make_summary_table(res, sim)

sim <- sim %>%
  mutate(
    Gamma_t = -Delta_t + Gamma_risk_t
  )


# # Print summary table (Table 3 in the text)
# make_summary_table(res, sim_trim)
# make_lp_decomposition_table <- function(res, sim) {
#   # Steady state values from calibration
#   lp_cal <- res$lp$components
#   LP_ss_total <- res$lp$LP_real
#
#   # Extract steady-state components
#   carry_ss <- lp_cal["carry"]
#   reserve_ss <- lp_cal["reserve"]
#   wedge_ss <- lp_cal["wedge"]
#   # Risk correction = Delta + Gamma_risk term
#   risk_ss <- lp_cal["Delta"] + lp_cal["Gamma_risk"]
#
#   # Simulated means (handle NA values)
#   carry_sim <- mean(sim$LP_carry, na.rm = TRUE)
#   reserve_sim <- mean(sim$LP_reserve, na.rm = TRUE)
#   wedge_sim <- mean(sim$LP_wedge, na.rm = TRUE)
#   # Risk correction in simulation: Delta_t - Gamma_risk_t
#   risk_sim <- mean(sim$Delta_t - sim$Gamma_risk_t, na.rm = TRUE)
#   LP_sim_total <- mean(sim$LP, na.rm = TRUE)
#
#   # Calculate shares (as percentage of total LP)
#   share_carry_ss <- 100 * carry_ss / LP_ss_total
#   share_reserve_ss <- 100 * reserve_ss / LP_ss_total
#   share_wedge_ss <- 100 * wedge_ss / LP_ss_total
#   share_risk_ss <- 100 * risk_ss / LP_ss_total
#
#   share_carry_sim <- 100 * carry_sim / LP_sim_total
#   share_reserve_sim <- 100 * reserve_sim / LP_sim_total
#   share_wedge_sim <- 100 * wedge_sim / LP_sim_total
#   share_risk_sim <- 100 * risk_sim / LP_sim_total
# #
#   # Create table
#   tab_lp <- data.frame(
#     Component = c("Bond-carry term", "Reserve drag", "Regulatory wedge", "Risk correction"),
#     Level_SS = c(carry_ss, reserve_ss, wedge_ss, risk_ss),
#     Share_SS = c(share_carry_ss, share_reserve_ss, share_wedge_ss, share_risk_ss),
#     Level_Sim = c(carry_sim, reserve_sim, wedge_sim, risk_sim),
#     Share_Sim = c(share_carry_sim, share_reserve_sim, share_wedge_sim, share_risk_sim)
#   )
#
#   # Generate LaTeX table
#   kable(
#     tab_lp,
#     format = "latex",
#     booktabs = TRUE,
#     digits = 3,
#     col.names = c("Component", "Level", "Share (\\%)", "Level", "Share (\\%)"),
#     caption = "Liquidity premium decomposition: steady state vs simulated means.",
#     label = "lp_decomp",
#     escape = FALSE
#   ) %>%
#     kableExtra::add_header_above(c(" " = 1, "Steady state" = 2, "Simulation" = 2))
# }

## 3. LaTeX table (Table 4 in the text)
kable(
  tab_order,
  format   = "latex",
  booktabs = TRUE,
  escape   = FALSE,   # keep LaTeX math/bold as-is
  align    = c("l","r"),
  caption  = "Ordering of real returns and implied spreads (per period)",
  col.names = c("Check / spread", "Value")
)
make_lp_decomposition_table <- function(res, sim) {
  # Steady state values from calibration
  lp_cal      <- res$lp$components
  LP_ss_total <- res$lp$LP_real

  # Extract steady-state components
  carry_ss      <- lp_cal["carry"]
  reserve_ss    <- lp_cal["reserve"]
  wedge_ss      <- lp_cal["wedge"]
  Delta_ss      <- lp_cal["Delta"]        # pricing wedge
  Gamma_risk_ss <- lp_cal["Gamma_risk"]   # covariance term Γ_risk
  risk_term_ss  <- -Gamma_risk_ss         # contribution of risk to LP is -Γ_risk

  # Simulated means (handle NA values)
  carry_sim      <- mean(sim$LP_carry,       na.rm = TRUE)
  reserve_sim    <- mean(sim$LP_reserve,     na.rm = TRUE)
  wedge_sim      <- mean(sim$LP_wedge,       na.rm = TRUE)
  Delta_sim      <- mean(sim$Delta_t,        na.rm = TRUE)
  Gamma_risk_sim <- mean(sim$Gamma_risk_t,   na.rm = TRUE)
  risk_term_sim  <- mean(-sim$Gamma_risk_t,  na.rm = TRUE)

  LP_sim_total <- mean(sim$LP, na.rm = TRUE)

  # Calculate shares (as percentage of total LP)
  share_carry_ss      <- 100 * carry_ss     / LP_ss_total
  share_reserve_ss    <- 100 * reserve_ss   / LP_ss_total
  share_wedge_ss      <- 100 * wedge_ss     / LP_ss_total
  share_Delta_ss      <- 100 * Delta_ss     / LP_ss_total
  share_risk_term_ss  <- 100 * risk_term_ss / LP_ss_total

  share_carry_sim     <- 100 * carry_sim     / LP_sim_total
  share_reserve_sim   <- 100 * reserve_sim   / LP_sim_total
  share_wedge_sim     <- 100 * wedge_sim     / LP_sim_total
  share_Delta_sim     <- 100 * Delta_sim     / LP_sim_total
  share_risk_term_sim <- 100 * risk_term_sim / LP_sim_total

  # Create table with Δ and risk reported separately
  tab_lp <- data.frame(
    Component = c(
      "Bond-carry term",
      "Reserve drag",
      "Regulatory wedge",
      "Pricing wedge ($\\Delta_t$)",
      "Risk term ($-\\Gamma_t^{\\text{risk}}$)"
    ),
    Level_SS = c(carry_ss, reserve_ss, wedge_ss, Delta_ss, risk_term_ss),
    Share_SS = c(share_carry_ss, share_reserve_ss, share_wedge_ss,
                 share_Delta_ss, share_risk_term_ss),
    Level_Sim = c(carry_sim, reserve_sim, wedge_sim, Delta_sim, risk_term_sim),
    Share_Sim = c(share_carry_sim, share_reserve_sim, share_wedge_sim,
                  share_Delta_sim, share_risk_term_sim)
  )

  # Generate LaTeX table
  kable(
    tab_lp,
    format   = "latex",
    booktabs = TRUE,
    digits   = 3,
    col.names = c("Component", "Level", "Share (\\%)", "Level", "Share (\\%)"),
    caption  = "Liquidity premium decomposition: steady state vs simulated means.",
    label    = "lp_decomp",
    escape   = FALSE
  ) %>%
    kableExtra::add_header_above(c(" " = 1, "Steady state" = 2, "Simulation" = 2))
}

# Trim burn-in period
sim_trim <- sim %>% filter(t >= 10)

# Print LP decomposition table (Table 5 in the text)
make_lp_decomposition_table(res, sim_trim)


##==========================================================================
## --- common calibration targets/parameters ---TABLE 6
## ---------------------------------------------
## Common targets and structural parameters
## ---------------------------------------------
targets_list <- list(
  RS = c(0.001, 0.010),
  RB = c(0.001, 0.012),
  RL = c(0.030, 0.040),
  RE = c(0.070, 0.090)
)



alpha  <- 0.33
delta  <- 0.06
gamma  <- 0.60
Phi    <- 1.00

Pi     <- 1.02
iR     <- 0.000
iSigma <- 0.05

varphi_cal <- 0.0510   # in calibration
varphi_sim <- 0.65     # in simulation

grid_n <- 101

## risk-moment inputs (for Gamma_risk_bar)
sigma_m     <- 0.05
sigma_sstar <- 0.04
rho_ms      <- 0.6
Em          <- 0.99

## pricing wedge in steady state
Delta_bar_common <- 0.063   # 3 bps

## ---------------------------------------------
## Helper: calibrate + simulate one case
## ---------------------------------------------
run_case <- function(theta_target, rho, kappa, Delta_bar, label = "case") {

  cat("=== Calibrating", label, "===\n")

  res <- calibrate_theta_policy_real(
    theta_target = theta_target,
    targets      = targets_list,
    alpha = alpha, delta = delta,
    gamma = gamma, Phi = Phi,
    rho   = rho, kappa = kappa,
    Pi = Pi, iR = iR, iSigma = iSigma,
    varphi = varphi_cal,
    grid_n = grid_n,
    closure = "solve_RB",
    sigma_m = sigma_m,
    sigma_sstar = sigma_sstar,
    rho_ms = rho_ms,
    Em = Em,
    Delta_bar = Delta_bar
  )

  cal <- res$calibration

  # A_bar from calibration (you already store A there)
  A_bar <- cal$A

  ## sanity check for A_bar
  if (!is.numeric(A_bar) || length(A_bar) != 1 || !is.finite(A_bar)) {
    stop("Calibration for ", label, " did not return a valid A.")
  }

  cat("theta =", cal$theta,
      "rho =", cal$rho,
      "kappa =", cal$kappa, "\n")
  cat("RS =", cal$RS,
      "RB =", cal$RB,
      "RL =", cal$RL,
      "RE =", cal$RE, "\n\n")

  sim <- simulate_path_real(
    T = 200,
    theta_bar = cal$theta,
    RSigma    = cal$RSigma,
    RR        = cal$RR,
    RL_calib  = res$rates_real["RL"],
    RE_calib  = res$rates_real["RE"],
    RB_calib  = res$rates_real["RB"],
    zbar      = cal$zbar,
    beta      = cal$beta,
    alpha = alpha, delta = delta, gamma = gamma,
    A_bar = A_bar,
    rho_A = 0.94, sigma_A = 0.01,
    rho_theta = 0.60, sigma_theta = 0.00,
    rho_Gamma = 0.90, sigma_Gamma = 0.00,
    Gamma_risk_bar = cal$Gamma_risk,  # from calibration
    rho_Delta = 0.95, sigma_Delta = 0.00,
    Delta_bar = cal$Delta_bar,        # = Delta_bar argument above
    rho_req = cal$rho, kappa = cal$kappa,
    varphi = varphi_sim, Pi = if (is.null(cal$Pi)) Pi else cal$Pi,
    bond_closure = "ZP_RB",
    RS_anchor   = cal$RS,
    lambda_RS   = 0.3,
    k0 = NULL, A0 = A_bar, theta0 = cal$theta,
    Gamma_risk0 = cal$Gamma_risk,
    Delta0      = cal$Delta_bar,
    seed = 123,
    logA = TRUE
  )

  return(list(calibration = cal, res = res, sim = sim))
}

## ---------------------------------------------
## 3. Run the three scenarios
## ---------------------------------------------

## Baseline
theta_baseline <- 0.50
rho_baseline   <- 0.10
kappa_baseline <- 0.1

base_case <- run_case(
  theta_target = theta_baseline,
  rho          = rho_baseline,
  kappa        = kappa_baseline,
  Delta_bar    = Delta_bar_common,
  label        = "Baseline"
)
cal_base  <- base_case$calibration
res_base  <- base_case$res
sim_base  <- base_case$sim

## Low regulation
theta_low <- 0.45
rho_low   <- 0.085
kappa_low <- 0.07

lowreg_case <- run_case(
  theta_target = theta_low,
  rho          = rho_low,
  kappa        = kappa_low,
  Delta_bar    = Delta_bar_common,
  label        = "Low regulation"
)
cal_low   <- lowreg_case$calibration
res_low   <- lowreg_case$res
sim_lowreg <- lowreg_case$sim

## High regulation
theta_high <- 0.6
rho_high   <- 0.15
kappa_high <- 0.12

highreg_case <- run_case(
  theta_target = theta_high,
  rho          = rho_high,
  kappa        = kappa_high,
  Delta_bar    = Delta_bar_common,
  label        = "High regulation"
)
cal_high   <- highreg_case$calibration
res_high   <- highreg_case$res
sim_highreg <- highreg_case$sim



sim_base#sim      # baseline θ, ρ, κ=sim_base
sim_lowreg    # “low regulation” experiment
sim_highreg   # “high regulation” experiment



## ---------- Panel A: mean real returns (annual, percent) ----------

summarise_returns <- function(sim) {
  c(
    Rs   = 100 * mean(sim$RS),
    RB   = 100 * mean(sim$RB),
    RL   = 100 * mean(sim$RL),
    RN   = 100 * mean(sim$RE),
    prem = 100 * mean(sim$RE - sim$RB)
  )
}

r_base   <- summarise_returns(sim_base)
r_low    <- summarise_returns(sim_lowreg)
r_high   <- summarise_returns(sim_highreg)

panelA <- data.frame(
  Metric = c("Deposits $R^s$",
             "Bills/Bonds $R^B$",
             "Loans $R^L$",
             "Equity $R^N$",
             "Equity premium $R^N-R^B$"),
  Baseline        = sprintf("%.2f", r_base),
  `Low regulation`  = sprintf("%.2f", r_low),
  `High regulation` = sprintf("%.2f", r_high),
  check.names = FALSE
)

## ---------- Panel B: LP decomposition shares (baseline only) ----------

lp_mom <- sim_base %>%
  summarise(
    mean_LP      = mean(LP),
    mean_carry   = mean(LP_carry),
    mean_reserve = mean(LP_reserve),
    mean_wedge   = mean(LP_wedge),
    mean_Delta   = mean(Delta_t),
    mean_Gammar  = mean(LP_risk)
  )

share_carry  <- 100 * lp_mom$mean_carry  / lp_mom$mean_LP
share_res    <- 100 * lp_mom$mean_reserve/ lp_mom$mean_LP
share_wedge  <- 100 * lp_mom$mean_wedge  / lp_mom$mean_LP
share_Delta  <- 100 * lp_mom$mean_Delta  / lp_mom$mean_LP
share_Gammar <- 100 * lp_mom$mean_Gammar / lp_mom$mean_LP  # will be small, ≈0 and negative

# Turn into the “≈ x% of LP” / “small, slightly negative” text
fmt_share <- function(x) sprintf("$\\approx %.0f\\%%$ of LP", x)

risk_text <- sprintf(
  "small, slightly negative (%.1f\\%% of LP)",
  share_Gammar
)

panelB <- data.frame(
  Metric = c("Bond--carry term",
             "Reserve drag",
             "Regulatory wedge",
             "Pricing wedge $(+\\Delta_t)$",
             "Risk term $(-\\Gamma_t^{\\text{risk}})$"),
  Baseline        = c(fmt_share(share_carry),
                      fmt_share(share_res),
                      fmt_share(share_wedge),
                      fmt_share(share_Delta),
                      risk_text),
  `Low regulation`  = "",
  `High regulation` = "",
  check.names = FALSE
)

# ---------------------------------------------
# Build counterfactual sims for Panel C (finite-difference sensitivities)
# ---------------------------------------------
# Assumes you already have:
#   - run_case(theta_target, rho, kappa, Delta_bar, label)
#   - sim_base from your baseline run_case(...)
#   - alpha, delta, gamma, Phi, Pi, iR, iSigma, varphi_cal, varphi_sim,
#     grid_n, sigma_m, sigma_sstar, rho_ms, Em, targets_list, Delta_bar_common
#
# The idea:
#  1) Re-calibrate at baseline+shock (theta+0.1, kappa+0.04, rho+0.05),
#  2) Simulate each path,
#  3) Compute sensitivity of equity-bond spread mean.

# --- Baseline parameters (edit to your baseline) ---
theta_base <- cal_base$theta
rho_base   <- cal_base$rho
kappa_base <- cal_base$kappa

# --- Step sizes (as in table labels) ---
dtheta <- 0.2
dkappa <- 0.05
drho   <- 0.1

# Helper to compute mean spread safely
mean_spread <- function(sim) mean(sim$RE - sim$RB, na.rm = TRUE)

# ---------------------------------------------------
# 1) θ + dθ experiment
# ---------------------------------------------------
theta_up_case <- run_case(
  theta_target = theta_base + dtheta,
  rho          = rho_base,
  kappa        = kappa_base,
  Delta_bar    = Delta_bar_common,
  label        = "theta+0.2"
)
sim_theta_up <- theta_up_case$sim


# ---------------------------------------------------
# 2) κ + dκ experiment
# ---------------------------------------------------
kappa_up_case <- run_case(
  theta_target = theta_base,
  rho          = rho_base,
  kappa        = kappa_base + dkappa,
  Delta_bar    = Delta_bar_common,
  label        = "kappa+0.05"
)
sim_kappa_up <- kappa_up_case$sim

# ---------------------------------------------------
# 3) ρ + dρ experiment
# ---------------------------------------------------
rho_up_case <- run_case(
  theta_target = theta_base,
  rho          = rho_base +drho,
  kappa        = kappa_base,
  Delta_bar    = Delta_bar_common,
  label        = "rho+0.05"
)
sim_rho_up <- rho_up_case$sim

# ---------------------------------------------------
# Compute "per +Δ" changes (matches your Panel C labels)
# ---------------------------------------------------
sens_theta <- mean_spread(sim_theta_up) - mean_spread(sim_base)
sens_kappa <- mean_spread(sim_kappa_up) - mean_spread(sim_base)
sens_rho   <- mean_spread(sim_rho_up)   - mean_spread(sim_base)

sens_theta_txt <- sprintf("$\\approx %+0.3f$", sens_theta)
sens_kappa_txt <- sprintf("$\\approx %+0.3f$", sens_kappa)
sens_rho_txt   <- sprintf("$\\approx %+0.3f$", sens_rho)

panelC <- data.frame(
  Metric = c(
    sprintf("$\\partial (R^N - R^B)/\\partial \\theta$ (per $+%.2f$)", dtheta),
    sprintf("$\\partial (R^N - R^B)/\\partial \\kappa$ (per $+%.2f$)", dkappa),
    sprintf("$\\partial (R^N - R^B)/\\partial \\rho$ (per $+%.2f$)",   drho)
  ),
  Baseline          = c(sens_theta_txt, sens_kappa_txt, sens_rho_txt),
  `Low regulation`  = c(sens_theta_txt, sens_kappa_txt, sens_rho_txt),
  `High regulation` = c(sens_theta_txt, sens_kappa_txt, sens_rho_txt),
  check.names = FALSE
)

panelC



## ---------- Combine and print LaTeX table ----------TABLE 6

summary_df <- bind_rows(panelA, panelB, panelC)

kable(
  summary_df,
  format   = "latex",
  booktabs = TRUE,
  escape   = FALSE,
  align    = c("l","c","c","c"),
  caption  = "Summary of quantitative results (annual, percent unless noted).",
  col.names = c("", "\\textbf{Baseline}",
                "\\textbf{Low regulation}",
                "\\textbf{High regulation}")
) %>%
  kable_styling(full_width = FALSE) %>%
  group_rows("\\textit{Panel A. Mean real returns}", 1, 5) %>%
  group_rows("\\textit{Panel B. Liquidity premium decomposition (baseline share)}", 6, 10) %>%
  group_rows("\\textit{Panel C. Sensitivities around baseline}", 11, 13)


#==============================================================================
##
############################################################
## Counterfactuals for regulation and the equity–bond spread
## θ (policy bond share), ρ (reserve requirement), κ (capital requirement)
############################################################

# Load packages (install if needed)
library(dplyr)
library(tidyr)
library(purrr)

#### 1. Baseline parameters ################################

params_baseline <- list(
  rho    = 0.10,   # reserve requirement
  kappa  = 0.1,   # capital requirement
  theta  = 0.40,   # policy bond share
  # preference / technology parameters (examples, fill with yours)
  beta   = 0.96,
  alpha  = 0.33,
  sigma  = 2.0,
  # financial parameters
  R_reserve = -0.02,  # real return on reserves
  loan_spread = 0.03, # R^σ
  phi_liquidity = 0.005  # liquidity parameter φ (example)
)

#### 2. Model solver (YOU must supply the core economics) ####
# This is a placeholder that you should replace with your actual
# steady-state or simulated-sample code.
#
# It should return at least:
# - R_B       : model-implied bond return
# - R_N       : equity return
# - R_s       : deposit rate
# - R_L       : loan rate
# - R_B_sdf   : SDF-implied risk-free rate (household Euler)
# - lp_decomp : named vector/list with components of the liquidity premium:
#       c(bond_carry = ..., reserve_drag = ..., regulatory_wedge = ...,
#         price_wedge = ..., risk_term = ...)
#
solve_model <- function(rho, kappa, theta, other_params) {
  # --- START: replace with your own model solution code ---

  # Example: pretend we have a calibrated mapping from (rho, kappa, theta)
  # to asset returns and LP decomposition. Replace this with your actual solver.

  # For illustration ONLY: small linear adjustments from the baseline values
  # to mimic your qualitative statements.
  adj_factor <- 1 - 0.5 * (rho - params_baseline$rho) -
    0.5 * (kappa - params_baseline$kappa) -
    0.8 * (theta - params_baseline$theta)

  adj_factor <- max(adj_factor, 0.2)  # avoid negatives in the toy example

  # Baseline target returns from the paper (approximate)
  R_s_base <- 0.001   # 0.1%
  R_B_base <- 0.009   # 0.9%
  R_L_base <- 0.035   # 3.5%
  R_N_base <- 0.08    # 8%

  # Adjusted returns (just to demonstrate direction)
  R_s <- R_s_base * adj_factor
  R_B <- R_B_base * adj_factor
  R_L <- R_L_base     # keep loans roughly fixed (spread mostly unchanged)
  R_N <- R_N_base     # equity return mostly pinned by technology/preferences

  # SDF-implied risk-free rate (toy; your model will produce this)
  R_B_sdf <- 0.03  # e.g., 3% implied by household Euler

  # Liquidity premium decomposition (levels)
  # LP_t = (R_B_sdf - R_B) = price_wedge + bond_carry + reserve_drag
  #        + regulatory_wedge - risk_term (sign convention from paper)
  lp_total <- R_B_sdf - R_B

  price_wedge     <- 0.9 * lp_total
  bond_carry      <- 0.06 * lp_total
  reserve_drag    <- 0.03 * lp_total
  regulatory_wedge <- 0.02 * lp_total
  risk_term       <- 0.01 * lp_total  # small and negative in contribution

  lp_decomp <- c(
    bond_carry       = bond_carry,
    reserve_drag     = reserve_drag,
    regulatory_wedge = regulatory_wedge,
    price_wedge      = price_wedge,
    risk_term        = risk_term
  )

  # --- END: replace up to here with your own model code ---

  list(
    R_B = R_B,
    R_N = R_N,
    R_s = R_s,
    R_L = R_L,
    R_B_sdf = R_B_sdf,
    lp_decomp = lp_decomp
  )
}

#### 3. Wrapper to compute key objects for a scenario ########

run_counterfactual <- function(theta, rho, kappa, label) {
  sol <- solve_model(
    rho = rho,
    kappa = kappa,
    theta = theta,
    other_params = params_baseline
  )

  equity_premium <- sol$R_N - sol$R_B
  liquidity_premium <- sum(sol$lp_decomp)

  price_wedge_share <- sol$lp_decomp["price_wedge"] / liquidity_premium

  tibble(
    scenario = label,
    theta = theta,
    rho   = rho,
    kappa = kappa,
    R_B   = sol$R_B,
    R_B_sdf = sol$R_B_sdf,
    R_N   = sol$R_N,
    equity_premium = equity_premium,
    liquidity_premium = liquidity_premium,
    price_wedge_share = price_wedge_share
  )
}

#### 4. Define baseline and counterfactual scenarios #########

scenarios <- tribble(
  ~scenario,        ~theta, ~rho,  ~kappa,
  "Baseline",        0.40,   0.10,  0.1,
  "Low theta",       0.20,   0.10,  0.1,
  "Low rho",         0.40,   0.05,  0.1,
  "Low kappa",       0.40,   0.10,  0.04,
  "All low",         0.020,   0.00,  0.00
)

results <- scenarios %>%
  pmap_dfr(~ run_counterfactual(
    theta = ..2,
    rho   = ..3,
    kappa = ..4,
    label = ..1
  ))

#### 5. Summarize results ####################################

# Table: effect of relaxing regulations on R^B, implied R^f, equity premium, LP
results_summary <- results %>%
  mutate(
    spread_to_sdf = R_B_sdf - R_B  # pricing wedge Δ_t
  ) %>%
  select(
    scenario, theta, rho, kappa,
    R_B, R_B_sdf, spread_to_sdf,
    R_N, equity_premium,
    liquidity_premium, price_wedge_share
  )

print(results_summary)

#### 6. Optional: show how equity–bond spread shrinks when regulation is muted ####

# Example: sort by "tightness" of regulation
results_summary %>%
  arrange(theta, rho, kappa) %>%
  select(scenario, equity_premium, liquidity_premium, spread_to_sdf) %>%
  print()

# You can also create plots, e.g. equity premium vs. theta:
# library(ggplot2)
# ggplot(results, aes(x = theta, y = equity_premium)) +
#   geom_point() +
#   geom_line() +
#   labs(x = expression(theta), y = "Equity-bond spread",
#        title = "Equity premium vs policy bond share θ")

#=============================================================================
# =============================================================================
# END OF SCRIPT
# =============================================================================

