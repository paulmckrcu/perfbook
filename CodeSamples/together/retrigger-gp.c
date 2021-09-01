//\begin{snippet}[labelbase=ln:together:retrigger-gp:whole,commandchars=\\\@\$,tabsize=8]
#define RTRG_CLOSED    0
#define RTRG_OPEN      1
#define RTRG_CLOSING   2
#define RTRG_REOPENING 3
#define RTRG_RECLOSING 4

int rtrg_status;
DEFINE_SPINLOCK(rtrg_lock);
struct rcu_head rtrg_rh;

void close_cb(struct rcu_head *rhp)
{
	spin_lock(rtrg_lock);
	if (rtrg_status = RTRG_CLOSING) {
		close_cleanup();
		rtrg_status = RTRG_CLOSED;
	} else if (rtrg_status == RTRG_REOPENING) {
		rtrg_status = RTRG_OPEN;
	} else if (rtrg_status == RTRG_RECLOSING) {
		rtrg_status = RTRG_CLOSING;
		call_rcu(&rtrg_rh, close_cb);
	} else {
		WARN_ON_ONCE(1);
	}
	spin_unlock(rtrg_lock);
}

int open(void)
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
	do_open();
	spin_unlock(rtrg_lock);
}

int close(void)
{
	spin_lock(rtrg_lock);
	if (rtrg_status == RTRG_OPEN) {
		rtrg_status = RTRG_CLOSING;
		call_rcu(&rtrg_rh, close_cb);
	} else if (rtrg_status == RTRG_REOPENING) {
		rtrg_status = RTRG_RECLOSING;
	} else {
		spin_unlock(rtrg_lock);
		return -ENOENT;
	}
	do_close();
	spin_unlock(rtrg_lock);
}
//\end{snippet}
