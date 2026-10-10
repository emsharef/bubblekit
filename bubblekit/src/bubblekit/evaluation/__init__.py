"""Tools for comparing bubble scores: forward outcomes, panel regressions, ROC/AUC, flag rates, alarm timing."""
from .outcomes import forward_outcomes, max_drawdown
from .regression import ols, cluster_se, twoway_se, driscoll_kraay_se, rank_within, forecast_regression
from .roc import auc, auc_bootstrap, roc_curve
from .alarms import first_alarm, alarm_lead, rates_by_group

__all__ = [
    "forward_outcomes", "max_drawdown", "ols", "cluster_se", "twoway_se", "driscoll_kraay_se", "rank_within",
    "forecast_regression", "auc", "auc_bootstrap", "roc_curve", "first_alarm", "alarm_lead", "rates_by_group",
]
