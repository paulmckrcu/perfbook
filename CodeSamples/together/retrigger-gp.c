//\begin{snippet}[labelbase=ln:together:retrigger-gp:whole,commandchars=\\\@\$,tabsize=8]
#define RTRG_CLOSED    0	//\lnlbl{states:b}
#define RTRG_OPEN      1
#define RTRG_CLOSING   2
#define RTRG_REOPENING 3
#define RTRG_RECLOSING 4	//\lnlbl{states:e}

int rtrg_status;		//\lnlbl{status}
DEFINE_SPINLOCK(rtrg_lock);	//\lnlbl{lock}
struct rcu_head rtrg_rh;

void close_cb(struct rcu_head *rhp)		//\lnlbl{close_cb:b}
{
	spin_lock(rtrg_lock);
	if (rtrg_status = RTRG_CLOSING) {
		close_cleanup();		//\lnlbl{cleanup}
		rtrg_status = RTRG_CLOSED;
	} else if (rtrg_status == RTRG_REOPENING) {
		rtrg_status = RTRG_OPEN;
	} else if (rtrg_status == RTRG_RECLOSING) {
		rtrg_status = RTRG_CLOSING;
		call_rcu(&rtrg_rh, close_cb);	//\lnlbl{call_rcu1}
	} else {
		WARN_ON_ONCE(1);
	}
	spin_unlock(rtrg_lock);
}						//\lnlbl{close_cb:e}

int open(void)					//\lnlbl{open:b}
{
	spin_lock(rtrg_lock);
	if (rtrg_status == RTRG_CLOSED) {
		rtrg_status = RTRG_OPEN;
	} else if (rtrg_status == RTRG_CLOSING ||
		   rtrg_status == RTRG_RECLOSING) {
		rtrg_status = RTRG_REOPENING;
	} else {
		spin_unlock(rtrg_lock);
		return -EBUSY;
	}
	do_open();				//\lnlbl{do_open}
	spin_unlock(rtrg_lock);
}						//\lnlbl{open:e}

int close(void)					//\lnlbl{close:b}
{
	spin_lock(rtrg_lock);
	if (rtrg_status == RTRG_OPEN) {
		rtrg_status = RTRG_CLOSING;
		call_rcu(&rtrg_rh, close_cb);	//\lnlbl{call_rcu2}
	} else if (rtrg_status == RTRG_REOPENING) {
		rtrg_status = RTRG_RECLOSING;
	} else {
		spin_unlock(rtrg_lock);
		return -ENOENT;
	}
	do_close();				//\lnlbl{do_close}
	spin_unlock(rtrg_lock);
}						//\lnlbl{close:e}
//\end{snippet}
