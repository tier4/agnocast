#include "agnocast/agnocast_timer.hpp"

#include "agnocast/agnocast_timer_info.hpp"

namespace agnocast
{

TimerBase::~TimerBase()
{
  remove_timer(timer_id_);
}

}  // namespace agnocast
