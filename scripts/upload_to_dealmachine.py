import csv
import requests
import os
import time
import re

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'data/leads_ghl_export.csv' 
BASE_URL = "https://api.dealmachine.com/public/v1/leads"
LIST_ID = "1254885" # Richland_Intel

def clean_address(addr):
    # Strip parentheses and standardize units
    addr = re.sub(r'\(.*?\)', '', addr)
    addr = re.sub(r'\bUNIT\b', '#', addr, flags=re.IGNORECASE)
    return addr.strip().strip(',')

def upload_leads():
    if not API_KEY:
        print("❌ API Key missing")
        return

    headers = {
        "Authorization": f"Bearer {API_KEY}",
        "Accept": "application/json"
    }

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        
        for row in reader:
            raw_addr = row.get('Property Address', '').strip()
            # Basic validation: must start with a digit and be reasonably short
            if not raw_addr or not raw_addr[0].isdigit() or len(raw_addr) > 120:
                continue

            addr = clean_address(raw_addr)
            city = row.get('Property City', 'Columbia').strip()
            zip_code = row.get('Property Zip', '').strip()
            
            # Initial Creation Payload (JSON)
            payload = {
                "address": addr,
                "city": city,
                "state": "SC",
                "zip": zip_code,
                "skip_trace": True,
                "lists": [int(LIST_ID)]
            }

            try:
                # 1. ATTEMPT TO CREATE (POST)
                response = requests.post(f"{BASE_URL}/", json=payload, headers=headers)
                res_data = response.json()
                
                # Check for ID and Error message
                lead_id = res_data.get('data', {}).get('id') if isinstance(res_data.get('data'), dict) else None
                error_info = res_data.get('error', {})
                error_msg = error_info.get('message', '') if isinstance(error_info, dict) else str(error_info)

                if response.status_code in [200, 201] and lead_id:
                    print(f"✅ Added: {addr}")
                
                elif "already added" in error_msg.lower() or lead_id:
                    # 2. IF EXISTS, USE THE ADD-TO-LIST ENDPOINT (FORM DATA)
                    # Use lead_id from the response
                    target_id = lead_id or res_data.get('data', {}).get('id')
                    
                    if target_id:
                        add_to_list_url = f"{BASE_URL}/{target_id}/add-to-list"
                        # Documentation shows this specific endpoint uses Form Data (multipart/form-data)
                        form_data = {'list_ids': LIST_ID}
                        
                        update_res = requests.post(add_to_list_url, data=form_data, headers=headers)
                        
                        if update_res.status_code == 200:
                            print(f"🔄 Synced: {addr} -> Richland_Intel")
                        else:
                            print(f"⚠️ Found {addr}, but List Sync failed: {update_res.text}")
                    else:
                        print(f"➖ Skipped: {addr} (Could not retrieve ID)")
                
                else:
                    print(f"❌ Failed: {addr} | {error_msg}")
            
            except Exception as e:
                print(f"⚠️ System Error: {addr} | {str(e)}")

            time.sleep(0.4)

if __name__ == "__main__":
    upload_leads()
